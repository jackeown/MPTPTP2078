%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:07 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 206 expanded)
%              Number of leaves         :   13 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  193 ( 593 expanded)
%              Number of equality atoms :   47 ( 120 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1669,plain,(
    $false ),
    inference(resolution,[],[f1660,f37])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f1660,plain,(
    ! [X15] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X15)),X15) ),
    inference(forward_demodulation,[],[f1659,f99])).

fof(f99,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f94,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(resolution,[],[f55,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f94,plain,(
    ! [X0] : k2_xboole_0(X0,k6_subset_1(X0,X0)) = X0 ),
    inference(resolution,[],[f54,f59])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1 ) ),
    inference(definition_unfolding,[],[f42,f39])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f1659,plain,(
    ! [X15] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X15)),k2_xboole_0(X15,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1658,f258])).

fof(f258,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f247,f61])).

fof(f247,plain,(
    ! [X2] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2)) ),
    inference(superposition,[],[f202,f61])).

fof(f202,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f201,f34])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f201,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f51,f35])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f1658,plain,(
    ! [X15] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X15)),k2_xboole_0(X15,k10_relat_1(sK1,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f1657,f644])).

fof(f644,plain,(
    ! [X4,X5] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X4),X5),k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f628])).

fof(f628,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k6_subset_1(k10_relat_1(sK1,X4),X5),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f56,f342])).

fof(f342,plain,(
    ! [X0,X1] : k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1)) ),
    inference(resolution,[],[f327,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(k6_subset_1(X0,X2),X1) ) ),
    inference(resolution,[],[f57,f55])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f39])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f327,plain,(
    ! [X1] : r1_tarski(k10_relat_1(sK1,X1),k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f319])).

fof(f319,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k10_relat_1(sK1,X1),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f56,f296])).

fof(f296,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f63,f34])).

fof(f63,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k1_xboole_0 = k6_subset_1(k10_relat_1(X3,X4),k1_relat_1(X3)) ) ),
    inference(resolution,[],[f55,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1657,plain,(
    ! [X15] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X15)),k2_xboole_0(X15,k10_relat_1(sK1,k1_xboole_0)))
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X15)),X15),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f1642,f34])).

fof(f1642,plain,(
    ! [X15] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X15)),k2_xboole_0(X15,k10_relat_1(sK1,k1_xboole_0)))
      | ~ v1_relat_1(sK1)
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X15)),X15),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f174,f485])).

fof(f485,plain,(
    ! [X1] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1)) ),
    inference(superposition,[],[f483,f218])).

fof(f218,plain,(
    ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f217,f34])).

fof(f217,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f216,f35])).

fof(f216,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f52,f36])).

fof(f36,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f483,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f482,f34])).

fof(f482,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f136,f35])).

fof(f136,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(X4,k10_relat_1(X4,X5)),X5) ) ),
    inference(resolution,[],[f43,f55])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f174,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(X6,k2_xboole_0(X7,k10_relat_1(X8,k9_relat_1(X8,k6_subset_1(X6,X7)))))
      | ~ v1_relat_1(X8)
      | ~ r1_tarski(k6_subset_1(X6,X7),k1_relat_1(X8)) ) ),
    inference(resolution,[],[f41,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f50,f39])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:06:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.50  % (5698)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.50  % (5676)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.51  % (5701)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (5680)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.51  % (5690)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.52  % (5693)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.52  % (5689)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.52  % (5685)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.52  % (5675)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.52  % (5678)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (5673)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.52  % (5695)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.52  % (5674)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.52  % (5697)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.53  % (5687)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.53  % (5677)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.53  % (5672)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.53  % (5684)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.53  % (5679)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.53  % (5701)Refutation not found, incomplete strategy% (5701)------------------------------
% 0.19/0.53  % (5701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (5701)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (5701)Memory used [KB]: 1663
% 0.19/0.53  % (5701)Time elapsed: 0.003 s
% 0.19/0.53  % (5701)------------------------------
% 0.19/0.53  % (5701)------------------------------
% 0.19/0.53  % (5684)Refutation not found, incomplete strategy% (5684)------------------------------
% 0.19/0.53  % (5684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (5684)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (5684)Memory used [KB]: 10618
% 0.19/0.53  % (5684)Time elapsed: 0.129 s
% 0.19/0.53  % (5684)------------------------------
% 0.19/0.53  % (5684)------------------------------
% 0.19/0.53  % (5682)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.53  % (5682)Refutation not found, incomplete strategy% (5682)------------------------------
% 0.19/0.53  % (5682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (5696)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.54  % (5694)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.54  % (5681)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.54  % (5688)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.54  % (5699)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.54  % (5692)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.54  % (5686)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.55  % (5683)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.55  % (5691)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.55  % (5682)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (5682)Memory used [KB]: 10618
% 0.19/0.55  % (5682)Time elapsed: 0.107 s
% 0.19/0.55  % (5682)------------------------------
% 0.19/0.55  % (5682)------------------------------
% 0.19/0.56  % (5688)Refutation not found, incomplete strategy% (5688)------------------------------
% 0.19/0.56  % (5688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (5688)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (5688)Memory used [KB]: 10618
% 0.19/0.56  % (5688)Time elapsed: 0.168 s
% 0.19/0.56  % (5688)------------------------------
% 0.19/0.56  % (5688)------------------------------
% 0.19/0.56  % (5700)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.56  % (5700)Refutation not found, incomplete strategy% (5700)------------------------------
% 0.19/0.56  % (5700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (5700)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (5700)Memory used [KB]: 10618
% 0.19/0.56  % (5700)Time elapsed: 0.169 s
% 0.19/0.56  % (5700)------------------------------
% 0.19/0.56  % (5700)------------------------------
% 1.83/0.61  % (5678)Refutation found. Thanks to Tanya!
% 1.83/0.61  % SZS status Theorem for theBenchmark
% 1.83/0.61  % SZS output start Proof for theBenchmark
% 1.83/0.61  fof(f1669,plain,(
% 1.83/0.61    $false),
% 1.83/0.61    inference(resolution,[],[f1660,f37])).
% 1.83/0.61  fof(f37,plain,(
% 1.83/0.61    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.83/0.61    inference(cnf_transformation,[],[f30])).
% 1.83/0.61  fof(f30,plain,(
% 1.83/0.61    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.83/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f29])).
% 1.83/0.61  fof(f29,plain,(
% 1.83/0.61    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.83/0.61    introduced(choice_axiom,[])).
% 1.83/0.61  fof(f16,plain,(
% 1.83/0.61    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.83/0.61    inference(flattening,[],[f15])).
% 1.83/0.61  fof(f15,plain,(
% 1.83/0.61    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.83/0.61    inference(ennf_transformation,[],[f14])).
% 1.83/0.61  fof(f14,negated_conjecture,(
% 1.83/0.61    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.83/0.61    inference(negated_conjecture,[],[f13])).
% 1.83/0.61  fof(f13,conjecture,(
% 1.83/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 1.83/0.61  fof(f1660,plain,(
% 1.83/0.61    ( ! [X15] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X15)),X15)) )),
% 1.83/0.61    inference(forward_demodulation,[],[f1659,f99])).
% 1.83/0.61  fof(f99,plain,(
% 1.83/0.61    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.83/0.61    inference(forward_demodulation,[],[f94,f61])).
% 1.83/0.61  fof(f61,plain,(
% 1.83/0.61    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 1.83/0.61    inference(resolution,[],[f55,f59])).
% 1.83/0.61  fof(f59,plain,(
% 1.83/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.83/0.61    inference(equality_resolution,[],[f45])).
% 1.83/0.61  fof(f45,plain,(
% 1.83/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.83/0.61    inference(cnf_transformation,[],[f32])).
% 1.83/0.61  fof(f32,plain,(
% 1.83/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.83/0.61    inference(flattening,[],[f31])).
% 1.83/0.61  fof(f31,plain,(
% 1.83/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.83/0.61    inference(nnf_transformation,[],[f1])).
% 1.83/0.61  fof(f1,axiom,(
% 1.83/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.83/0.61  fof(f55,plain,(
% 1.83/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 1.83/0.61    inference(definition_unfolding,[],[f48,f39])).
% 1.83/0.61  fof(f39,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f7])).
% 1.83/0.61  fof(f7,axiom,(
% 1.83/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.83/0.61  fof(f48,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f33])).
% 1.83/0.61  fof(f33,plain,(
% 1.83/0.61    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.83/0.61    inference(nnf_transformation,[],[f2])).
% 1.83/0.61  fof(f2,axiom,(
% 1.83/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.83/0.61  fof(f94,plain,(
% 1.83/0.61    ( ! [X0] : (k2_xboole_0(X0,k6_subset_1(X0,X0)) = X0) )),
% 1.83/0.61    inference(resolution,[],[f54,f59])).
% 1.83/0.61  fof(f54,plain,(
% 1.83/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1) )),
% 1.83/0.61    inference(definition_unfolding,[],[f42,f39])).
% 1.83/0.61  fof(f42,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f20])).
% 1.83/0.61  fof(f20,plain,(
% 1.83/0.61    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 1.83/0.61    inference(ennf_transformation,[],[f6])).
% 1.83/0.61  fof(f6,axiom,(
% 1.83/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 1.83/0.61  fof(f1659,plain,(
% 1.83/0.61    ( ! [X15] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X15)),k2_xboole_0(X15,k1_xboole_0))) )),
% 1.83/0.61    inference(forward_demodulation,[],[f1658,f258])).
% 1.83/0.61  fof(f258,plain,(
% 1.83/0.61    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.83/0.61    inference(forward_demodulation,[],[f247,f61])).
% 1.83/0.61  fof(f247,plain,(
% 1.83/0.61    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2))) )),
% 1.83/0.61    inference(superposition,[],[f202,f61])).
% 1.83/0.61  fof(f202,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 1.83/0.61    inference(subsumption_resolution,[],[f201,f34])).
% 1.83/0.61  fof(f34,plain,(
% 1.83/0.61    v1_relat_1(sK1)),
% 1.83/0.61    inference(cnf_transformation,[],[f30])).
% 1.83/0.61  fof(f201,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.83/0.61    inference(resolution,[],[f51,f35])).
% 1.83/0.61  fof(f35,plain,(
% 1.83/0.61    v1_funct_1(sK1)),
% 1.83/0.61    inference(cnf_transformation,[],[f30])).
% 1.83/0.61  fof(f51,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f26])).
% 1.83/0.61  fof(f26,plain,(
% 1.83/0.61    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.83/0.61    inference(flattening,[],[f25])).
% 1.83/0.61  fof(f25,plain,(
% 1.83/0.61    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.83/0.61    inference(ennf_transformation,[],[f10])).
% 1.83/0.61  fof(f10,axiom,(
% 1.83/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 1.83/0.61  fof(f1658,plain,(
% 1.83/0.61    ( ! [X15] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X15)),k2_xboole_0(X15,k10_relat_1(sK1,k1_xboole_0)))) )),
% 1.83/0.61    inference(subsumption_resolution,[],[f1657,f644])).
% 1.83/0.61  fof(f644,plain,(
% 1.83/0.61    ( ! [X4,X5] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X4),X5),k1_relat_1(sK1))) )),
% 1.83/0.61    inference(trivial_inequality_removal,[],[f628])).
% 1.83/0.61  fof(f628,plain,(
% 1.83/0.61    ( ! [X4,X5] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k6_subset_1(k10_relat_1(sK1,X4),X5),k1_relat_1(sK1))) )),
% 1.83/0.61    inference(superposition,[],[f56,f342])).
% 1.83/0.61  fof(f342,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1))) )),
% 1.83/0.61    inference(resolution,[],[f327,f71])).
% 1.83/0.61  fof(f71,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(k6_subset_1(X0,X2),X1)) )),
% 1.83/0.61    inference(resolution,[],[f57,f55])).
% 1.83/0.61  fof(f57,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.83/0.61    inference(definition_unfolding,[],[f49,f39])).
% 1.83/0.61  fof(f49,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f23])).
% 1.83/0.61  fof(f23,plain,(
% 1.83/0.61    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.83/0.61    inference(ennf_transformation,[],[f3])).
% 1.83/0.61  fof(f3,axiom,(
% 1.83/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 1.83/0.61  fof(f327,plain,(
% 1.83/0.61    ( ! [X1] : (r1_tarski(k10_relat_1(sK1,X1),k1_relat_1(sK1))) )),
% 1.83/0.61    inference(trivial_inequality_removal,[],[f319])).
% 1.83/0.61  fof(f319,plain,(
% 1.83/0.61    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k10_relat_1(sK1,X1),k1_relat_1(sK1))) )),
% 1.83/0.61    inference(superposition,[],[f56,f296])).
% 1.83/0.61  fof(f296,plain,(
% 1.83/0.61    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 1.83/0.61    inference(resolution,[],[f63,f34])).
% 1.83/0.61  fof(f63,plain,(
% 1.83/0.61    ( ! [X4,X3] : (~v1_relat_1(X3) | k1_xboole_0 = k6_subset_1(k10_relat_1(X3,X4),k1_relat_1(X3))) )),
% 1.83/0.61    inference(resolution,[],[f55,f40])).
% 1.83/0.61  fof(f40,plain,(
% 1.83/0.61    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f17])).
% 1.83/0.61  fof(f17,plain,(
% 1.83/0.61    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.83/0.61    inference(ennf_transformation,[],[f8])).
% 1.83/0.61  fof(f8,axiom,(
% 1.83/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.83/0.61  fof(f56,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 1.83/0.61    inference(definition_unfolding,[],[f47,f39])).
% 1.83/0.61  fof(f47,plain,(
% 1.83/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.83/0.61    inference(cnf_transformation,[],[f33])).
% 1.83/0.61  fof(f1657,plain,(
% 1.83/0.61    ( ! [X15] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X15)),k2_xboole_0(X15,k10_relat_1(sK1,k1_xboole_0))) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X15)),X15),k1_relat_1(sK1))) )),
% 1.83/0.61    inference(subsumption_resolution,[],[f1642,f34])).
% 1.83/0.61  fof(f1642,plain,(
% 1.83/0.61    ( ! [X15] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X15)),k2_xboole_0(X15,k10_relat_1(sK1,k1_xboole_0))) | ~v1_relat_1(sK1) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X15)),X15),k1_relat_1(sK1))) )),
% 1.83/0.61    inference(superposition,[],[f174,f485])).
% 1.83/0.61  fof(f485,plain,(
% 1.83/0.61    ( ! [X1] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1))) )),
% 1.83/0.61    inference(superposition,[],[f483,f218])).
% 1.83/0.61  fof(f218,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 1.83/0.61    inference(subsumption_resolution,[],[f217,f34])).
% 1.83/0.61  fof(f217,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.83/0.61    inference(subsumption_resolution,[],[f216,f35])).
% 1.83/0.61  fof(f216,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.83/0.61    inference(resolution,[],[f52,f36])).
% 1.83/0.61  fof(f36,plain,(
% 1.83/0.61    v2_funct_1(sK1)),
% 1.83/0.61    inference(cnf_transformation,[],[f30])).
% 1.83/0.61  fof(f52,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f28])).
% 1.83/0.61  fof(f28,plain,(
% 1.83/0.61    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.83/0.61    inference(flattening,[],[f27])).
% 1.83/0.61  fof(f27,plain,(
% 1.83/0.61    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.83/0.61    inference(ennf_transformation,[],[f9])).
% 1.83/0.61  fof(f9,axiom,(
% 1.83/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 1.83/0.61  fof(f483,plain,(
% 1.83/0.61    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 1.83/0.61    inference(subsumption_resolution,[],[f482,f34])).
% 1.83/0.61  fof(f482,plain,(
% 1.83/0.61    ( ! [X0] : (~v1_relat_1(sK1) | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 1.83/0.61    inference(resolution,[],[f136,f35])).
% 1.83/0.61  fof(f136,plain,(
% 1.83/0.61    ( ! [X4,X5] : (~v1_funct_1(X4) | ~v1_relat_1(X4) | k1_xboole_0 = k6_subset_1(k9_relat_1(X4,k10_relat_1(X4,X5)),X5)) )),
% 1.83/0.61    inference(resolution,[],[f43,f55])).
% 1.83/0.61  fof(f43,plain,(
% 1.83/0.61    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f22])).
% 1.83/0.61  fof(f22,plain,(
% 1.83/0.61    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.83/0.61    inference(flattening,[],[f21])).
% 1.83/0.61  fof(f21,plain,(
% 1.83/0.61    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.83/0.61    inference(ennf_transformation,[],[f11])).
% 1.83/0.61  fof(f11,axiom,(
% 1.83/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 1.83/0.61  fof(f174,plain,(
% 1.83/0.61    ( ! [X6,X8,X7] : (r1_tarski(X6,k2_xboole_0(X7,k10_relat_1(X8,k9_relat_1(X8,k6_subset_1(X6,X7))))) | ~v1_relat_1(X8) | ~r1_tarski(k6_subset_1(X6,X7),k1_relat_1(X8))) )),
% 1.83/0.61    inference(resolution,[],[f41,f58])).
% 1.83/0.61  fof(f58,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.83/0.61    inference(definition_unfolding,[],[f50,f39])).
% 1.83/0.61  fof(f50,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f24])).
% 1.83/0.61  fof(f24,plain,(
% 1.83/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.83/0.61    inference(ennf_transformation,[],[f5])).
% 1.83/0.61  fof(f5,axiom,(
% 1.83/0.61    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.83/0.61  fof(f41,plain,(
% 1.83/0.61    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f19])).
% 1.83/0.61  fof(f19,plain,(
% 1.83/0.61    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.83/0.61    inference(flattening,[],[f18])).
% 1.83/0.61  fof(f18,plain,(
% 1.83/0.61    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.83/0.61    inference(ennf_transformation,[],[f12])).
% 1.83/0.61  fof(f12,axiom,(
% 1.83/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.83/0.61  % SZS output end Proof for theBenchmark
% 1.83/0.61  % (5678)------------------------------
% 1.83/0.61  % (5678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.61  % (5678)Termination reason: Refutation
% 1.83/0.61  
% 1.83/0.61  % (5678)Memory used [KB]: 11769
% 1.83/0.61  % (5678)Time elapsed: 0.196 s
% 1.83/0.61  % (5678)------------------------------
% 1.83/0.61  % (5678)------------------------------
% 1.83/0.62  % (5671)Success in time 0.255 s
%------------------------------------------------------------------------------
