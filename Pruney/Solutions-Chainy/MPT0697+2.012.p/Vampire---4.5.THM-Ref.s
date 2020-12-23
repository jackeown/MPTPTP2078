%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:07 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 224 expanded)
%              Number of leaves         :   15 (  54 expanded)
%              Depth                    :   18
%              Number of atoms          :  203 ( 684 expanded)
%              Number of equality atoms :   49 ( 124 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1836,plain,(
    $false ),
    inference(resolution,[],[f1822,f41])).

fof(f41,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f33])).

fof(f33,plain,
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

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f1822,plain,(
    ! [X3] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X3)),X3) ),
    inference(trivial_inequality_removal,[],[f1803])).

fof(f1803,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X3)),X3) ) ),
    inference(superposition,[],[f61,f1751])).

fof(f1751,plain,(
    ! [X8] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8) ),
    inference(forward_demodulation,[],[f1750,f262])).

fof(f262,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f254,f76])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1) ),
    inference(resolution,[],[f60,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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

fof(f254,plain,(
    ! [X2] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2)) ),
    inference(superposition,[],[f200,f76])).

fof(f200,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f199,f38])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f199,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f57,f39])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f1750,plain,(
    ! [X8] : k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8) ),
    inference(subsumption_resolution,[],[f1749,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1749,plain,(
    ! [X8] :
      ( ~ r1_tarski(k1_xboole_0,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8))
      | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8) ) ),
    inference(forward_demodulation,[],[f1748,f262])).

fof(f1748,plain,(
    ! [X8] :
      ( ~ r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8))
      | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8) ) ),
    inference(subsumption_resolution,[],[f1747,f475])).

fof(f475,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1)) ),
    inference(resolution,[],[f436,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f55,f43])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f436,plain,(
    ! [X6,X7] : r1_tarski(k10_relat_1(sK1,X6),k2_xboole_0(X7,k1_relat_1(sK1))) ),
    inference(superposition,[],[f300,f342])).

fof(f342,plain,(
    ! [X0] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f67,f38])).

fof(f67,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | k1_relat_1(X2) = k2_xboole_0(k10_relat_1(X2,X3),k1_relat_1(X2)) ) ),
    inference(resolution,[],[f46,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f300,plain,(
    ! [X2,X0,X1] : r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(resolution,[],[f72,f63])).

fof(f72,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(k2_xboole_0(X2,X5),X4)
      | r1_tarski(X2,k2_xboole_0(X3,X4)) ) ),
    inference(resolution,[],[f56,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f1747,plain,(
    ! [X8] :
      ( ~ r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8))
      | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8)
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f1733,f38])).

fof(f1733,plain,(
    ! [X8] :
      ( ~ r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8))
      | ~ v1_relat_1(sK1)
      | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8)
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f183,f503])).

fof(f503,plain,(
    ! [X1] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1)) ),
    inference(superposition,[],[f454,f219])).

fof(f219,plain,(
    ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f218,f38])).

fof(f218,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f217,f39])).

fof(f217,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f58,f40])).

fof(f40,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f454,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f453,f38])).

fof(f453,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f150,f39])).

fof(f150,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(X4,k10_relat_1(X4,X5)),X5) ) ),
    inference(resolution,[],[f48,f60])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f183,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k10_relat_1(X3,k9_relat_1(X3,X2)),X2)
      | ~ v1_relat_1(X3)
      | k10_relat_1(X3,k9_relat_1(X3,X2)) = X2
      | ~ r1_tarski(X2,k1_relat_1(X3)) ) ),
    inference(resolution,[],[f45,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f43])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:24:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (3791)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.50  % (3790)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (3775)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (3782)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.50  % (3770)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.50  % (3773)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (3771)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (3769)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (3783)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (3774)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (3786)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (3777)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (3772)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (3768)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (3789)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (3787)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (3794)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (3793)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (3781)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (3785)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (3776)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (3779)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (3788)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (3778)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (3797)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (3797)Refutation not found, incomplete strategy% (3797)------------------------------
% 0.21/0.52  % (3797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3797)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3797)Memory used [KB]: 1663
% 0.21/0.52  % (3797)Time elapsed: 0.003 s
% 0.21/0.52  % (3797)------------------------------
% 0.21/0.52  % (3797)------------------------------
% 0.21/0.52  % (3795)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (3780)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (3796)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (3780)Refutation not found, incomplete strategy% (3780)------------------------------
% 0.21/0.54  % (3780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3796)Refutation not found, incomplete strategy% (3796)------------------------------
% 0.21/0.54  % (3796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3778)Refutation not found, incomplete strategy% (3778)------------------------------
% 0.21/0.54  % (3778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3778)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3778)Memory used [KB]: 10618
% 0.21/0.54  % (3778)Time elapsed: 0.139 s
% 0.21/0.54  % (3778)------------------------------
% 0.21/0.54  % (3778)------------------------------
% 1.43/0.54  % (3780)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (3780)Memory used [KB]: 10618
% 1.43/0.54  % (3780)Time elapsed: 0.144 s
% 1.43/0.54  % (3780)------------------------------
% 1.43/0.54  % (3780)------------------------------
% 1.43/0.55  % (3796)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (3796)Memory used [KB]: 10618
% 1.43/0.55  % (3796)Time elapsed: 0.142 s
% 1.43/0.55  % (3796)------------------------------
% 1.43/0.55  % (3796)------------------------------
% 1.43/0.55  % (3784)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.43/0.56  % (3784)Refutation not found, incomplete strategy% (3784)------------------------------
% 1.43/0.56  % (3784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (3792)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.43/0.56  % (3784)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (3784)Memory used [KB]: 10618
% 1.43/0.56  % (3784)Time elapsed: 0.163 s
% 1.43/0.56  % (3784)------------------------------
% 1.43/0.56  % (3784)------------------------------
% 1.61/0.60  % (3774)Refutation found. Thanks to Tanya!
% 1.61/0.60  % SZS status Theorem for theBenchmark
% 1.61/0.61  % SZS output start Proof for theBenchmark
% 1.61/0.61  fof(f1836,plain,(
% 1.61/0.61    $false),
% 1.61/0.61    inference(resolution,[],[f1822,f41])).
% 1.61/0.61  fof(f41,plain,(
% 1.61/0.61    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.61/0.61    inference(cnf_transformation,[],[f34])).
% 1.61/0.61  fof(f34,plain,(
% 1.61/0.61    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.61/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f33])).
% 1.61/0.61  fof(f33,plain,(
% 1.61/0.61    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.61/0.61    introduced(choice_axiom,[])).
% 1.61/0.61  fof(f18,plain,(
% 1.61/0.61    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.61/0.61    inference(flattening,[],[f17])).
% 1.61/0.61  fof(f17,plain,(
% 1.61/0.61    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.61/0.61    inference(ennf_transformation,[],[f16])).
% 1.61/0.61  fof(f16,negated_conjecture,(
% 1.61/0.61    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.61/0.61    inference(negated_conjecture,[],[f15])).
% 1.61/0.61  fof(f15,conjecture,(
% 1.61/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 1.61/0.61  fof(f1822,plain,(
% 1.61/0.61    ( ! [X3] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X3)),X3)) )),
% 1.61/0.61    inference(trivial_inequality_removal,[],[f1803])).
% 1.61/0.61  fof(f1803,plain,(
% 1.61/0.61    ( ! [X3] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X3)),X3)) )),
% 1.61/0.61    inference(superposition,[],[f61,f1751])).
% 1.61/0.61  fof(f1751,plain,(
% 1.61/0.61    ( ! [X8] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8)) )),
% 1.61/0.61    inference(forward_demodulation,[],[f1750,f262])).
% 1.61/0.61  fof(f262,plain,(
% 1.61/0.61    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.61/0.61    inference(forward_demodulation,[],[f254,f76])).
% 1.61/0.61  fof(f76,plain,(
% 1.61/0.61    ( ! [X1] : (k1_xboole_0 = k6_subset_1(X1,X1)) )),
% 1.61/0.61    inference(resolution,[],[f60,f63])).
% 1.61/0.61  fof(f63,plain,(
% 1.61/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.61/0.61    inference(equality_resolution,[],[f50])).
% 1.61/0.61  fof(f50,plain,(
% 1.61/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.61/0.61    inference(cnf_transformation,[],[f36])).
% 1.61/0.61  fof(f36,plain,(
% 1.61/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/0.61    inference(flattening,[],[f35])).
% 1.61/0.61  fof(f35,plain,(
% 1.61/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/0.61    inference(nnf_transformation,[],[f1])).
% 1.61/0.61  fof(f1,axiom,(
% 1.61/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.61/0.61  fof(f60,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 1.61/0.61    inference(definition_unfolding,[],[f53,f43])).
% 1.61/0.61  fof(f43,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f9])).
% 1.61/0.61  fof(f9,axiom,(
% 1.61/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.61/0.61  fof(f53,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f37])).
% 1.61/0.61  fof(f37,plain,(
% 1.61/0.61    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.61/0.61    inference(nnf_transformation,[],[f2])).
% 1.61/0.61  fof(f2,axiom,(
% 1.61/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.61/0.61  fof(f254,plain,(
% 1.61/0.61    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2))) )),
% 1.61/0.61    inference(superposition,[],[f200,f76])).
% 1.61/0.61  fof(f200,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 1.61/0.61    inference(subsumption_resolution,[],[f199,f38])).
% 1.61/0.61  fof(f38,plain,(
% 1.61/0.61    v1_relat_1(sK1)),
% 1.61/0.61    inference(cnf_transformation,[],[f34])).
% 1.61/0.61  fof(f199,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.61/0.61    inference(resolution,[],[f57,f39])).
% 1.61/0.61  fof(f39,plain,(
% 1.61/0.61    v1_funct_1(sK1)),
% 1.61/0.61    inference(cnf_transformation,[],[f34])).
% 1.61/0.61  fof(f57,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f30])).
% 1.61/0.61  fof(f30,plain,(
% 1.61/0.61    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.61/0.61    inference(flattening,[],[f29])).
% 1.61/0.61  fof(f29,plain,(
% 1.61/0.61    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.61/0.61    inference(ennf_transformation,[],[f12])).
% 1.61/0.61  fof(f12,axiom,(
% 1.61/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 1.61/0.61  fof(f1750,plain,(
% 1.61/0.61    ( ! [X8] : (k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8)) )),
% 1.61/0.61    inference(subsumption_resolution,[],[f1749,f42])).
% 1.61/0.61  fof(f42,plain,(
% 1.61/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f6])).
% 1.61/0.61  fof(f6,axiom,(
% 1.61/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.61/0.61  fof(f1749,plain,(
% 1.61/0.61    ( ! [X8] : (~r1_tarski(k1_xboole_0,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8)) | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8)) )),
% 1.61/0.61    inference(forward_demodulation,[],[f1748,f262])).
% 1.61/0.61  fof(f1748,plain,(
% 1.61/0.61    ( ! [X8] : (~r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8)) | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8)) )),
% 1.61/0.61    inference(subsumption_resolution,[],[f1747,f475])).
% 1.61/0.61  fof(f475,plain,(
% 1.61/0.61    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1))) )),
% 1.61/0.61    inference(resolution,[],[f436,f62])).
% 1.61/0.61  fof(f62,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 1.61/0.61    inference(definition_unfolding,[],[f55,f43])).
% 1.61/0.61  fof(f55,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.61/0.61    inference(cnf_transformation,[],[f27])).
% 1.61/0.61  fof(f27,plain,(
% 1.61/0.61    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.61/0.61    inference(ennf_transformation,[],[f7])).
% 1.61/0.61  fof(f7,axiom,(
% 1.61/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.61/0.61  fof(f436,plain,(
% 1.61/0.61    ( ! [X6,X7] : (r1_tarski(k10_relat_1(sK1,X6),k2_xboole_0(X7,k1_relat_1(sK1)))) )),
% 1.61/0.61    inference(superposition,[],[f300,f342])).
% 1.61/0.61  fof(f342,plain,(
% 1.61/0.61    ( ! [X0] : (k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 1.61/0.61    inference(resolution,[],[f67,f38])).
% 1.61/0.61  fof(f67,plain,(
% 1.61/0.61    ( ! [X2,X3] : (~v1_relat_1(X2) | k1_relat_1(X2) = k2_xboole_0(k10_relat_1(X2,X3),k1_relat_1(X2))) )),
% 1.61/0.61    inference(resolution,[],[f46,f44])).
% 1.61/0.61  fof(f44,plain,(
% 1.61/0.61    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f19])).
% 1.61/0.61  fof(f19,plain,(
% 1.61/0.61    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.61/0.61    inference(ennf_transformation,[],[f10])).
% 1.61/0.61  fof(f10,axiom,(
% 1.61/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.61/0.61  fof(f46,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.61/0.61    inference(cnf_transformation,[],[f22])).
% 1.61/0.62  fof(f22,plain,(
% 1.61/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.61/0.62    inference(ennf_transformation,[],[f5])).
% 1.61/0.62  fof(f5,axiom,(
% 1.61/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.61/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.61/0.62  fof(f300,plain,(
% 1.61/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 1.61/0.62    inference(resolution,[],[f72,f63])).
% 1.61/0.62  fof(f72,plain,(
% 1.61/0.62    ( ! [X4,X2,X5,X3] : (~r1_tarski(k2_xboole_0(X2,X5),X4) | r1_tarski(X2,k2_xboole_0(X3,X4))) )),
% 1.61/0.62    inference(resolution,[],[f56,f54])).
% 1.61/0.62  fof(f54,plain,(
% 1.61/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.61/0.62    inference(cnf_transformation,[],[f26])).
% 1.61/0.62  fof(f26,plain,(
% 1.61/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.61/0.62    inference(ennf_transformation,[],[f3])).
% 1.61/0.62  fof(f3,axiom,(
% 1.61/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.61/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.61/0.62  fof(f56,plain,(
% 1.61/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.61/0.62    inference(cnf_transformation,[],[f28])).
% 1.61/0.62  fof(f28,plain,(
% 1.61/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.61/0.62    inference(ennf_transformation,[],[f4])).
% 1.61/0.62  fof(f4,axiom,(
% 1.61/0.62    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.61/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.61/0.62  fof(f1747,plain,(
% 1.61/0.62    ( ! [X8] : (~r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8)) | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_relat_1(sK1))) )),
% 1.61/0.62    inference(subsumption_resolution,[],[f1733,f38])).
% 1.61/0.62  fof(f1733,plain,(
% 1.61/0.62    ( ! [X8] : (~r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8)) | ~v1_relat_1(sK1) | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_relat_1(sK1))) )),
% 1.61/0.62    inference(superposition,[],[f183,f503])).
% 1.61/0.62  fof(f503,plain,(
% 1.61/0.62    ( ! [X1] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1))) )),
% 1.61/0.62    inference(superposition,[],[f454,f219])).
% 1.61/0.62  fof(f219,plain,(
% 1.61/0.62    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 1.61/0.62    inference(subsumption_resolution,[],[f218,f38])).
% 1.61/0.62  fof(f218,plain,(
% 1.61/0.62    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.61/0.62    inference(subsumption_resolution,[],[f217,f39])).
% 1.61/0.62  fof(f217,plain,(
% 1.61/0.62    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.61/0.62    inference(resolution,[],[f58,f40])).
% 1.61/0.62  fof(f40,plain,(
% 1.61/0.62    v2_funct_1(sK1)),
% 1.61/0.62    inference(cnf_transformation,[],[f34])).
% 1.61/0.62  fof(f58,plain,(
% 1.61/0.62    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.61/0.62    inference(cnf_transformation,[],[f32])).
% 1.61/0.62  fof(f32,plain,(
% 1.61/0.62    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.61/0.62    inference(flattening,[],[f31])).
% 1.61/0.62  fof(f31,plain,(
% 1.61/0.62    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.61/0.62    inference(ennf_transformation,[],[f11])).
% 1.61/0.62  fof(f11,axiom,(
% 1.61/0.62    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.61/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 1.61/0.62  fof(f454,plain,(
% 1.61/0.62    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 1.61/0.62    inference(subsumption_resolution,[],[f453,f38])).
% 1.61/0.62  fof(f453,plain,(
% 1.61/0.62    ( ! [X0] : (~v1_relat_1(sK1) | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 1.61/0.62    inference(resolution,[],[f150,f39])).
% 1.61/0.62  fof(f150,plain,(
% 1.61/0.62    ( ! [X4,X5] : (~v1_funct_1(X4) | ~v1_relat_1(X4) | k1_xboole_0 = k6_subset_1(k9_relat_1(X4,k10_relat_1(X4,X5)),X5)) )),
% 1.61/0.62    inference(resolution,[],[f48,f60])).
% 1.61/0.62  fof(f48,plain,(
% 1.61/0.62    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.61/0.62    inference(cnf_transformation,[],[f25])).
% 1.61/0.62  fof(f25,plain,(
% 1.61/0.62    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.61/0.62    inference(flattening,[],[f24])).
% 1.61/0.62  fof(f24,plain,(
% 1.61/0.62    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.61/0.62    inference(ennf_transformation,[],[f13])).
% 1.61/0.62  fof(f13,axiom,(
% 1.61/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.61/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.61/0.62  fof(f183,plain,(
% 1.61/0.62    ( ! [X2,X3] : (~r1_tarski(k10_relat_1(X3,k9_relat_1(X3,X2)),X2) | ~v1_relat_1(X3) | k10_relat_1(X3,k9_relat_1(X3,X2)) = X2 | ~r1_tarski(X2,k1_relat_1(X3))) )),
% 1.61/0.62    inference(resolution,[],[f45,f51])).
% 1.61/0.62  fof(f51,plain,(
% 1.61/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.61/0.62    inference(cnf_transformation,[],[f36])).
% 1.61/0.62  fof(f45,plain,(
% 1.61/0.62    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.61/0.62    inference(cnf_transformation,[],[f21])).
% 1.61/0.62  fof(f21,plain,(
% 1.61/0.62    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.61/0.62    inference(flattening,[],[f20])).
% 1.61/0.62  fof(f20,plain,(
% 1.61/0.62    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.61/0.62    inference(ennf_transformation,[],[f14])).
% 1.61/0.62  fof(f14,axiom,(
% 1.61/0.62    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.61/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.61/0.62  fof(f61,plain,(
% 1.61/0.62    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 1.61/0.62    inference(definition_unfolding,[],[f52,f43])).
% 1.61/0.62  fof(f52,plain,(
% 1.61/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.61/0.62    inference(cnf_transformation,[],[f37])).
% 1.61/0.62  % SZS output end Proof for theBenchmark
% 1.61/0.62  % (3774)------------------------------
% 1.61/0.62  % (3774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.62  % (3774)Termination reason: Refutation
% 1.61/0.62  
% 1.61/0.62  % (3774)Memory used [KB]: 11769
% 1.61/0.62  % (3774)Time elapsed: 0.170 s
% 1.61/0.62  % (3774)------------------------------
% 1.61/0.62  % (3774)------------------------------
% 1.61/0.62  % (3767)Success in time 0.268 s
%------------------------------------------------------------------------------
