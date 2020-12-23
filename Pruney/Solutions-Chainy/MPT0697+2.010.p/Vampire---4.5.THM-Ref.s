%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:07 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 256 expanded)
%              Number of leaves         :   12 (  62 expanded)
%              Depth                    :   18
%              Number of atoms          :  194 ( 769 expanded)
%              Number of equality atoms :   51 ( 156 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f853,plain,(
    $false ),
    inference(resolution,[],[f838,f35])).

fof(f35,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f27])).

fof(f27,plain,
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

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f838,plain,(
    ! [X3] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X3)),X3) ),
    inference(trivial_inequality_removal,[],[f820])).

fof(f820,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X3)),X3) ) ),
    inference(superposition,[],[f52,f774])).

fof(f774,plain,(
    ! [X10] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10) ),
    inference(forward_demodulation,[],[f773,f175])).

fof(f175,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f167,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(resolution,[],[f51,f54])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f167,plain,(
    ! [X2] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2)) ),
    inference(superposition,[],[f150,f56])).

fof(f150,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f149,f32])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f149,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f48,f33])).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f773,plain,(
    ! [X10] : k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10) ),
    inference(subsumption_resolution,[],[f772,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f63,f54])).

fof(f63,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f53,f56])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f38])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f772,plain,(
    ! [X10] :
      ( ~ r1_tarski(k1_xboole_0,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10))
      | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10) ) ),
    inference(forward_demodulation,[],[f771,f175])).

fof(f771,plain,(
    ! [X10] :
      ( ~ r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10))
      | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10) ) ),
    inference(subsumption_resolution,[],[f770,f408])).

fof(f408,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f399])).

fof(f399,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f52,f221])).

fof(f221,plain,(
    ! [X19,X18] : k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,X18),X19),k1_relat_1(sK1)) ),
    inference(resolution,[],[f61,f96])).

fof(f96,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f95,f32])).

fof(f95,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f39,f66])).

fof(f66,plain,(
    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(resolution,[],[f37,f32])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(k6_subset_1(X0,X2),X1) ) ),
    inference(resolution,[],[f53,f51])).

fof(f770,plain,(
    ! [X10] :
      ( ~ r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10))
      | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10)
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f756,f32])).

fof(f756,plain,(
    ! [X10] :
      ( ~ r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10))
      | ~ v1_relat_1(sK1)
      | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10)
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f130,f322])).

fof(f322,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) ),
    inference(superposition,[],[f317,f179])).

fof(f179,plain,(
    ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f178,f32])).

fof(f178,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f177,f33])).

fof(f177,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f317,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f316,f32])).

fof(f316,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f108,f33])).

fof(f108,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(X4,k10_relat_1(X4,X5)),X5) ) ),
    inference(resolution,[],[f41,f51])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f40,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f38])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (10699)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (10713)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (10712)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (10721)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (10716)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (10697)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (10701)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (10703)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (10698)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (10720)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (10711)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (10702)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (10707)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (10700)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (10707)Refutation not found, incomplete strategy% (10707)------------------------------
% 0.20/0.52  % (10707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10704)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (10722)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.31/0.53  % (10707)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (10707)Memory used [KB]: 10618
% 1.31/0.53  % (10707)Time elapsed: 0.127 s
% 1.31/0.53  % (10707)------------------------------
% 1.31/0.53  % (10707)------------------------------
% 1.31/0.53  % (10726)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.31/0.53  % (10717)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.31/0.53  % (10723)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.31/0.53  % (10726)Refutation not found, incomplete strategy% (10726)------------------------------
% 1.31/0.53  % (10726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (10726)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (10726)Memory used [KB]: 10618
% 1.31/0.53  % (10726)Time elapsed: 0.131 s
% 1.31/0.53  % (10726)------------------------------
% 1.31/0.53  % (10726)------------------------------
% 1.31/0.54  % (10727)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.31/0.54  % (10727)Refutation not found, incomplete strategy% (10727)------------------------------
% 1.31/0.54  % (10727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (10727)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (10727)Memory used [KB]: 1663
% 1.31/0.54  % (10727)Time elapsed: 0.001 s
% 1.31/0.54  % (10727)------------------------------
% 1.31/0.54  % (10727)------------------------------
% 1.31/0.54  % (10724)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.31/0.54  % (10708)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.31/0.54  % (10706)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.31/0.54  % (10725)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.31/0.54  % (10703)Refutation found. Thanks to Tanya!
% 1.31/0.54  % SZS status Theorem for theBenchmark
% 1.31/0.54  % (10718)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.31/0.54  % (10719)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.31/0.55  % (10705)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.49/0.55  % (10709)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.49/0.55  % (10715)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.49/0.55  % (10714)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.49/0.55  % (10709)Refutation not found, incomplete strategy% (10709)------------------------------
% 1.49/0.55  % (10709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (10709)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (10709)Memory used [KB]: 10618
% 1.49/0.55  % (10709)Time elapsed: 0.150 s
% 1.49/0.55  % (10709)------------------------------
% 1.49/0.55  % (10709)------------------------------
% 1.49/0.55  % (10714)Refutation not found, incomplete strategy% (10714)------------------------------
% 1.49/0.55  % (10714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (10714)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (10714)Memory used [KB]: 10618
% 1.49/0.56  % (10714)Time elapsed: 0.145 s
% 1.49/0.56  % (10714)------------------------------
% 1.49/0.56  % (10714)------------------------------
% 1.49/0.56  % SZS output start Proof for theBenchmark
% 1.49/0.56  fof(f853,plain,(
% 1.49/0.56    $false),
% 1.49/0.56    inference(resolution,[],[f838,f35])).
% 1.49/0.56  fof(f35,plain,(
% 1.49/0.56    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.49/0.56    inference(cnf_transformation,[],[f28])).
% 1.49/0.56  fof(f28,plain,(
% 1.49/0.56    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f27])).
% 1.49/0.56  fof(f27,plain,(
% 1.49/0.56    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f15,plain,(
% 1.49/0.56    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.49/0.56    inference(flattening,[],[f14])).
% 1.49/0.56  fof(f14,plain,(
% 1.49/0.56    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.49/0.56    inference(ennf_transformation,[],[f13])).
% 1.49/0.56  fof(f13,negated_conjecture,(
% 1.49/0.56    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.49/0.56    inference(negated_conjecture,[],[f12])).
% 1.49/0.56  fof(f12,conjecture,(
% 1.49/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 1.49/0.56  fof(f838,plain,(
% 1.49/0.56    ( ! [X3] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X3)),X3)) )),
% 1.49/0.56    inference(trivial_inequality_removal,[],[f820])).
% 1.49/0.56  fof(f820,plain,(
% 1.49/0.56    ( ! [X3] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X3)),X3)) )),
% 1.49/0.56    inference(superposition,[],[f52,f774])).
% 1.49/0.56  fof(f774,plain,(
% 1.49/0.56    ( ! [X10] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10)) )),
% 1.49/0.56    inference(forward_demodulation,[],[f773,f175])).
% 1.49/0.56  fof(f175,plain,(
% 1.49/0.56    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.49/0.56    inference(forward_demodulation,[],[f167,f56])).
% 1.49/0.56  fof(f56,plain,(
% 1.49/0.56    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 1.49/0.56    inference(resolution,[],[f51,f54])).
% 1.49/0.56  fof(f54,plain,(
% 1.49/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.49/0.56    inference(equality_resolution,[],[f43])).
% 1.49/0.56  fof(f43,plain,(
% 1.49/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.49/0.56    inference(cnf_transformation,[],[f30])).
% 1.49/0.56  fof(f30,plain,(
% 1.49/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.56    inference(flattening,[],[f29])).
% 1.49/0.56  fof(f29,plain,(
% 1.49/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.56    inference(nnf_transformation,[],[f1])).
% 1.49/0.56  fof(f1,axiom,(
% 1.49/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.56  fof(f51,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f46,f38])).
% 1.49/0.56  fof(f38,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f5])).
% 1.49/0.56  fof(f5,axiom,(
% 1.49/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.49/0.56  fof(f46,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f31])).
% 1.49/0.56  fof(f31,plain,(
% 1.49/0.56    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.49/0.56    inference(nnf_transformation,[],[f2])).
% 1.49/0.56  fof(f2,axiom,(
% 1.49/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.49/0.56  fof(f167,plain,(
% 1.49/0.56    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2))) )),
% 1.49/0.56    inference(superposition,[],[f150,f56])).
% 1.49/0.56  fof(f150,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f149,f32])).
% 1.49/0.56  fof(f32,plain,(
% 1.49/0.56    v1_relat_1(sK1)),
% 1.49/0.56    inference(cnf_transformation,[],[f28])).
% 1.49/0.56  fof(f149,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.49/0.56    inference(resolution,[],[f48,f33])).
% 1.49/0.56  fof(f33,plain,(
% 1.49/0.56    v1_funct_1(sK1)),
% 1.49/0.56    inference(cnf_transformation,[],[f28])).
% 1.49/0.56  fof(f48,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f24])).
% 1.49/0.56  fof(f24,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.49/0.56    inference(flattening,[],[f23])).
% 1.49/0.56  fof(f23,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.49/0.56    inference(ennf_transformation,[],[f9])).
% 1.49/0.56  fof(f9,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 1.49/0.56  fof(f773,plain,(
% 1.49/0.56    ( ! [X10] : (k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f772,f64])).
% 1.49/0.56  fof(f64,plain,(
% 1.49/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.49/0.56    inference(resolution,[],[f63,f54])).
% 1.49/0.56  fof(f63,plain,(
% 1.49/0.56    ( ! [X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(k1_xboole_0,X3)) )),
% 1.49/0.56    inference(superposition,[],[f53,f56])).
% 1.49/0.56  fof(f53,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f47,f38])).
% 1.49/0.56  fof(f47,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f22])).
% 1.49/0.56  fof(f22,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.49/0.56    inference(ennf_transformation,[],[f3])).
% 1.49/0.56  fof(f3,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 1.49/0.56  fof(f772,plain,(
% 1.49/0.56    ( ! [X10] : (~r1_tarski(k1_xboole_0,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10)) | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10)) )),
% 1.49/0.56    inference(forward_demodulation,[],[f771,f175])).
% 1.49/0.56  fof(f771,plain,(
% 1.49/0.56    ( ! [X10] : (~r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10)) | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f770,f408])).
% 1.49/0.56  fof(f408,plain,(
% 1.49/0.56    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1))) )),
% 1.49/0.56    inference(trivial_inequality_removal,[],[f399])).
% 1.49/0.56  fof(f399,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1))) )),
% 1.49/0.56    inference(superposition,[],[f52,f221])).
% 1.49/0.56  fof(f221,plain,(
% 1.49/0.56    ( ! [X19,X18] : (k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,X18),X19),k1_relat_1(sK1))) )),
% 1.49/0.56    inference(resolution,[],[f61,f96])).
% 1.49/0.56  fof(f96,plain,(
% 1.49/0.56    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f95,f32])).
% 1.49/0.56  fof(f95,plain,(
% 1.49/0.56    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.49/0.56    inference(superposition,[],[f39,f66])).
% 1.49/0.56  fof(f66,plain,(
% 1.49/0.56    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)),
% 1.49/0.56    inference(resolution,[],[f37,f32])).
% 1.49/0.56  fof(f37,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f16])).
% 1.49/0.56  fof(f16,plain,(
% 1.49/0.56    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f6])).
% 1.49/0.56  fof(f6,axiom,(
% 1.49/0.56    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.49/0.56  fof(f39,plain,(
% 1.49/0.56    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f17])).
% 1.49/0.56  fof(f17,plain,(
% 1.49/0.56    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.49/0.56    inference(ennf_transformation,[],[f7])).
% 1.49/0.56  fof(f7,axiom,(
% 1.49/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).
% 1.49/0.56  fof(f61,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(k6_subset_1(X0,X2),X1)) )),
% 1.49/0.56    inference(resolution,[],[f53,f51])).
% 1.49/0.56  fof(f770,plain,(
% 1.49/0.56    ( ! [X10] : (~r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10)) | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_relat_1(sK1))) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f756,f32])).
% 1.49/0.56  fof(f756,plain,(
% 1.49/0.56    ( ! [X10] : (~r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10)) | ~v1_relat_1(sK1) | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_relat_1(sK1))) )),
% 1.49/0.56    inference(superposition,[],[f130,f322])).
% 1.49/0.56  fof(f322,plain,(
% 1.49/0.56    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))) )),
% 1.49/0.56    inference(superposition,[],[f317,f179])).
% 1.49/0.56  fof(f179,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f178,f32])).
% 1.49/0.56  fof(f178,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f177,f33])).
% 1.49/0.56  fof(f177,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.49/0.56    inference(resolution,[],[f49,f34])).
% 1.49/0.56  fof(f34,plain,(
% 1.49/0.56    v2_funct_1(sK1)),
% 1.49/0.56    inference(cnf_transformation,[],[f28])).
% 1.49/0.56  fof(f49,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f26])).
% 1.49/0.56  fof(f26,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.49/0.56    inference(flattening,[],[f25])).
% 1.49/0.56  fof(f25,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.49/0.56    inference(ennf_transformation,[],[f8])).
% 1.49/0.56  fof(f8,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 1.49/0.56  fof(f317,plain,(
% 1.49/0.56    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f316,f32])).
% 1.49/0.56  fof(f316,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_relat_1(sK1) | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 1.49/0.56    inference(resolution,[],[f108,f33])).
% 1.49/0.56  fof(f108,plain,(
% 1.49/0.56    ( ! [X4,X5] : (~v1_funct_1(X4) | ~v1_relat_1(X4) | k1_xboole_0 = k6_subset_1(k9_relat_1(X4,k10_relat_1(X4,X5)),X5)) )),
% 1.49/0.56    inference(resolution,[],[f41,f51])).
% 1.49/0.56  fof(f41,plain,(
% 1.49/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f21])).
% 1.49/0.56  fof(f21,plain,(
% 1.49/0.56    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.49/0.56    inference(flattening,[],[f20])).
% 1.49/0.56  fof(f20,plain,(
% 1.49/0.56    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.49/0.56    inference(ennf_transformation,[],[f10])).
% 1.49/0.56  fof(f10,axiom,(
% 1.49/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 1.49/0.56  fof(f130,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v1_relat_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) )),
% 1.49/0.56    inference(resolution,[],[f40,f44])).
% 1.49/0.56  fof(f44,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f30])).
% 1.49/0.56  fof(f40,plain,(
% 1.49/0.56    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f19])).
% 1.49/0.56  fof(f19,plain,(
% 1.49/0.56    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.49/0.56    inference(flattening,[],[f18])).
% 1.49/0.56  fof(f18,plain,(
% 1.49/0.56    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.49/0.56    inference(ennf_transformation,[],[f11])).
% 1.49/0.56  fof(f11,axiom,(
% 1.49/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.49/0.56  fof(f52,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f45,f38])).
% 1.49/0.56  fof(f45,plain,(
% 1.49/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.49/0.56    inference(cnf_transformation,[],[f31])).
% 1.49/0.56  % SZS output end Proof for theBenchmark
% 1.49/0.56  % (10703)------------------------------
% 1.49/0.56  % (10703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (10703)Termination reason: Refutation
% 1.49/0.56  
% 1.49/0.56  % (10703)Memory used [KB]: 11129
% 1.49/0.56  % (10703)Time elapsed: 0.142 s
% 1.49/0.56  % (10703)------------------------------
% 1.49/0.56  % (10703)------------------------------
% 1.49/0.57  % (10693)Success in time 0.203 s
%------------------------------------------------------------------------------
