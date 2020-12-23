%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:06 EST 2020

% Result     : Theorem 3.23s
% Output     : Refutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 221 expanded)
%              Number of leaves         :   15 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  215 ( 633 expanded)
%              Number of equality atoms :   47 ( 126 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4017,plain,(
    $false ),
    inference(resolution,[],[f4005,f53])).

fof(f53,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f43])).

fof(f43,plain,
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

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f4005,plain,(
    ! [X8] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8) ),
    inference(forward_demodulation,[],[f4004,f132])).

fof(f132,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f127,f86])).

fof(f86,plain,(
    ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1) ),
    inference(resolution,[],[f78,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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

fof(f127,plain,(
    ! [X1] : k2_xboole_0(X1,k6_subset_1(X1,X1)) = X1 ),
    inference(resolution,[],[f77,f83])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1 ) ),
    inference(definition_unfolding,[],[f59,f56])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f4004,plain,(
    ! [X8] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X8)),k2_xboole_0(X8,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f4003,f673])).

fof(f673,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f661,f86])).

fof(f661,plain,(
    ! [X2] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2)) ),
    inference(superposition,[],[f349,f86])).

fof(f349,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f348,f50])).

fof(f50,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f348,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f71,f51])).

fof(f51,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f4003,plain,(
    ! [X8] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X8)),k2_xboole_0(X8,k10_relat_1(sK1,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f4002,f1163])).

fof(f1163,plain,(
    ! [X47,X48] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X47),X48),k1_relat_1(sK1)) ),
    inference(resolution,[],[f1106,f794])).

fof(f794,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k10_relat_1(sK1,X2))
      | r1_tarski(X1,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f787,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f787,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f777])).

fof(f777,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f79,f740])).

fof(f740,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f89,f50])).

fof(f89,plain,(
    ! [X8,X7] :
      ( ~ v1_relat_1(X7)
      | k1_xboole_0 = k6_subset_1(k10_relat_1(X7,X8),k1_relat_1(X7)) ) ),
    inference(resolution,[],[f78,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f56])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1106,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(resolution,[],[f1099,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f69,f56])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f1099,plain,(
    ! [X4,X5] : r1_tarski(X4,k2_xboole_0(X5,X4)) ),
    inference(trivial_inequality_removal,[],[f1086])).

fof(f1086,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X4,k2_xboole_0(X5,X4)) ) ),
    inference(superposition,[],[f79,f721])).

fof(f721,plain,(
    ! [X2,X3] : k1_xboole_0 = k6_subset_1(X2,k2_xboole_0(X3,X2)) ),
    inference(resolution,[],[f88,f83])).

fof(f88,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X4,X6)
      | k1_xboole_0 = k6_subset_1(X4,k2_xboole_0(X5,X6)) ) ),
    inference(resolution,[],[f78,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f4002,plain,(
    ! [X8] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X8)),k2_xboole_0(X8,k10_relat_1(sK1,k1_xboole_0)))
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f3986,f50])).

fof(f3986,plain,(
    ! [X8] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X8)),k2_xboole_0(X8,k10_relat_1(sK1,k1_xboole_0)))
      | ~ v1_relat_1(sK1)
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f313,f1268])).

fof(f1268,plain,(
    ! [X1] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1)) ),
    inference(superposition,[],[f1265,f578])).

fof(f578,plain,(
    ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f577,f50])).

fof(f577,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f576,f51])).

fof(f576,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f72,f52])).

fof(f52,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f1265,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f1264,f50])).

fof(f1264,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f225,f51])).

fof(f225,plain,(
    ! [X8,X7] :
      ( ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(X7,k10_relat_1(X7,X8)),X8) ) ),
    inference(resolution,[],[f60,f78])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f313,plain,(
    ! [X10,X11,X9] :
      ( r1_tarski(X9,k2_xboole_0(X10,k10_relat_1(X11,k9_relat_1(X11,k6_subset_1(X9,X10)))))
      | ~ v1_relat_1(X11)
      | ~ r1_tarski(k6_subset_1(X9,X10),k1_relat_1(X11)) ) ),
    inference(resolution,[],[f58,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f70,f56])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:46:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (23891)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (23906)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.50  % (23895)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (23896)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (23907)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (23894)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (23892)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (23893)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (23899)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (23898)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (23907)Refutation not found, incomplete strategy% (23907)------------------------------
% 0.21/0.52  % (23907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23907)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23907)Memory used [KB]: 10618
% 0.21/0.52  % (23907)Time elapsed: 0.117 s
% 0.21/0.52  % (23907)------------------------------
% 0.21/0.52  % (23907)------------------------------
% 0.21/0.52  % (23911)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (23915)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (23914)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (23903)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (23897)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (23917)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (23916)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (23913)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (23919)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (23920)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (23910)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (23905)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (23918)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (23908)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (23912)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (23909)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (23901)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (23904)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (23902)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (23900)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.25/0.66  % (23921)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.23/0.81  % (23897)Refutation found. Thanks to Tanya!
% 3.23/0.81  % SZS status Theorem for theBenchmark
% 3.23/0.81  % SZS output start Proof for theBenchmark
% 3.23/0.81  fof(f4017,plain,(
% 3.23/0.81    $false),
% 3.23/0.81    inference(resolution,[],[f4005,f53])).
% 3.23/0.81  fof(f53,plain,(
% 3.23/0.81    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 3.23/0.81    inference(cnf_transformation,[],[f44])).
% 3.23/0.81  fof(f44,plain,(
% 3.23/0.81    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 3.23/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f43])).
% 3.23/0.81  fof(f43,plain,(
% 3.23/0.81    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 3.23/0.81    introduced(choice_axiom,[])).
% 3.23/0.81  fof(f22,plain,(
% 3.23/0.81    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.23/0.81    inference(flattening,[],[f21])).
% 3.23/0.81  fof(f21,plain,(
% 3.23/0.81    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.23/0.81    inference(ennf_transformation,[],[f20])).
% 3.23/0.81  fof(f20,negated_conjecture,(
% 3.23/0.81    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 3.23/0.81    inference(negated_conjecture,[],[f19])).
% 3.23/0.81  fof(f19,conjecture,(
% 3.23/0.81    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 3.23/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 3.23/0.81  fof(f4005,plain,(
% 3.23/0.81    ( ! [X8] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8)) )),
% 3.23/0.81    inference(forward_demodulation,[],[f4004,f132])).
% 3.23/0.81  fof(f132,plain,(
% 3.23/0.81    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 3.23/0.81    inference(forward_demodulation,[],[f127,f86])).
% 3.23/0.81  fof(f86,plain,(
% 3.23/0.81    ( ! [X1] : (k1_xboole_0 = k6_subset_1(X1,X1)) )),
% 3.23/0.81    inference(resolution,[],[f78,f83])).
% 3.23/0.81  fof(f83,plain,(
% 3.23/0.81    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.23/0.81    inference(equality_resolution,[],[f62])).
% 3.23/0.81  fof(f62,plain,(
% 3.23/0.81    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.23/0.81    inference(cnf_transformation,[],[f46])).
% 3.23/0.81  fof(f46,plain,(
% 3.23/0.81    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/0.81    inference(flattening,[],[f45])).
% 3.23/0.81  fof(f45,plain,(
% 3.23/0.81    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/0.81    inference(nnf_transformation,[],[f1])).
% 3.23/0.81  fof(f1,axiom,(
% 3.23/0.81    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.23/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.23/0.81  fof(f78,plain,(
% 3.23/0.81    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 3.23/0.81    inference(definition_unfolding,[],[f65,f56])).
% 3.23/0.81  fof(f56,plain,(
% 3.23/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.23/0.81    inference(cnf_transformation,[],[f12])).
% 3.23/0.81  fof(f12,axiom,(
% 3.23/0.81    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.23/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.23/0.81  fof(f65,plain,(
% 3.23/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.23/0.81    inference(cnf_transformation,[],[f47])).
% 3.23/0.81  fof(f47,plain,(
% 3.23/0.81    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.23/0.81    inference(nnf_transformation,[],[f2])).
% 3.23/0.81  fof(f2,axiom,(
% 3.23/0.81    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.23/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.23/0.81  fof(f127,plain,(
% 3.23/0.81    ( ! [X1] : (k2_xboole_0(X1,k6_subset_1(X1,X1)) = X1) )),
% 3.23/0.81    inference(resolution,[],[f77,f83])).
% 3.23/0.81  fof(f77,plain,(
% 3.23/0.81    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1) )),
% 3.23/0.81    inference(definition_unfolding,[],[f59,f56])).
% 3.23/0.81  fof(f59,plain,(
% 3.23/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.23/0.81    inference(cnf_transformation,[],[f26])).
% 3.23/0.81  fof(f26,plain,(
% 3.23/0.81    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 3.23/0.81    inference(ennf_transformation,[],[f10])).
% 3.23/0.81  fof(f10,axiom,(
% 3.23/0.81    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 3.23/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 3.23/0.81  fof(f4004,plain,(
% 3.23/0.81    ( ! [X8] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X8)),k2_xboole_0(X8,k1_xboole_0))) )),
% 3.23/0.81    inference(forward_demodulation,[],[f4003,f673])).
% 3.23/0.81  fof(f673,plain,(
% 3.23/0.81    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 3.23/0.81    inference(forward_demodulation,[],[f661,f86])).
% 3.23/0.81  fof(f661,plain,(
% 3.23/0.81    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2))) )),
% 3.23/0.81    inference(superposition,[],[f349,f86])).
% 3.23/0.81  fof(f349,plain,(
% 3.23/0.81    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 3.23/0.81    inference(subsumption_resolution,[],[f348,f50])).
% 3.23/0.81  fof(f50,plain,(
% 3.23/0.81    v1_relat_1(sK1)),
% 3.23/0.81    inference(cnf_transformation,[],[f44])).
% 3.23/0.81  fof(f348,plain,(
% 3.23/0.81    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 3.23/0.81    inference(resolution,[],[f71,f51])).
% 3.23/0.81  fof(f51,plain,(
% 3.23/0.81    v1_funct_1(sK1)),
% 3.23/0.81    inference(cnf_transformation,[],[f44])).
% 3.23/0.81  fof(f71,plain,(
% 3.23/0.81    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.23/0.81    inference(cnf_transformation,[],[f36])).
% 3.23/0.81  fof(f36,plain,(
% 3.23/0.81    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.23/0.81    inference(flattening,[],[f35])).
% 3.23/0.81  fof(f35,plain,(
% 3.23/0.81    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.23/0.81    inference(ennf_transformation,[],[f16])).
% 3.23/0.81  fof(f16,axiom,(
% 3.23/0.81    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 3.23/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 3.23/0.81  fof(f4003,plain,(
% 3.23/0.81    ( ! [X8] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X8)),k2_xboole_0(X8,k10_relat_1(sK1,k1_xboole_0)))) )),
% 3.23/0.81    inference(subsumption_resolution,[],[f4002,f1163])).
% 3.23/0.81  fof(f1163,plain,(
% 3.23/0.81    ( ! [X47,X48] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X47),X48),k1_relat_1(sK1))) )),
% 3.23/0.81    inference(resolution,[],[f1106,f794])).
% 3.23/0.81  fof(f794,plain,(
% 3.23/0.81    ( ! [X2,X1] : (~r1_tarski(X1,k10_relat_1(sK1,X2)) | r1_tarski(X1,k1_relat_1(sK1))) )),
% 3.23/0.81    inference(resolution,[],[f787,f73])).
% 3.23/0.81  fof(f73,plain,(
% 3.23/0.81    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.23/0.81    inference(cnf_transformation,[],[f40])).
% 3.23/0.81  fof(f40,plain,(
% 3.23/0.81    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.23/0.81    inference(flattening,[],[f39])).
% 3.23/0.81  fof(f39,plain,(
% 3.23/0.81    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.23/0.81    inference(ennf_transformation,[],[f6])).
% 3.23/0.81  fof(f6,axiom,(
% 3.23/0.81    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.23/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.23/0.81  fof(f787,plain,(
% 3.23/0.81    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 3.23/0.81    inference(trivial_inequality_removal,[],[f777])).
% 3.23/0.81  fof(f777,plain,(
% 3.23/0.81    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 3.23/0.81    inference(superposition,[],[f79,f740])).
% 3.23/0.81  fof(f740,plain,(
% 3.23/0.81    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 3.23/0.81    inference(resolution,[],[f89,f50])).
% 3.23/0.81  fof(f89,plain,(
% 3.23/0.81    ( ! [X8,X7] : (~v1_relat_1(X7) | k1_xboole_0 = k6_subset_1(k10_relat_1(X7,X8),k1_relat_1(X7))) )),
% 3.23/0.81    inference(resolution,[],[f78,f57])).
% 3.23/0.81  fof(f57,plain,(
% 3.23/0.81    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.23/0.81    inference(cnf_transformation,[],[f23])).
% 3.23/0.81  fof(f23,plain,(
% 3.23/0.81    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.23/0.81    inference(ennf_transformation,[],[f13])).
% 3.23/0.81  fof(f13,axiom,(
% 3.23/0.81    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 3.23/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 3.23/0.81  fof(f79,plain,(
% 3.23/0.81    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 3.23/0.81    inference(definition_unfolding,[],[f64,f56])).
% 3.23/0.81  fof(f64,plain,(
% 3.23/0.81    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.23/0.81    inference(cnf_transformation,[],[f47])).
% 3.23/0.81  fof(f1106,plain,(
% 3.23/0.81    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 3.23/0.81    inference(resolution,[],[f1099,f81])).
% 3.23/0.81  fof(f81,plain,(
% 3.23/0.81    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 3.23/0.81    inference(definition_unfolding,[],[f69,f56])).
% 3.23/0.81  fof(f69,plain,(
% 3.23/0.81    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.23/0.81    inference(cnf_transformation,[],[f33])).
% 3.23/0.81  fof(f33,plain,(
% 3.23/0.81    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.23/0.81    inference(ennf_transformation,[],[f8])).
% 3.23/0.81  fof(f8,axiom,(
% 3.23/0.81    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.23/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 3.23/0.81  fof(f1099,plain,(
% 3.23/0.81    ( ! [X4,X5] : (r1_tarski(X4,k2_xboole_0(X5,X4))) )),
% 3.23/0.81    inference(trivial_inequality_removal,[],[f1086])).
% 3.23/0.81  fof(f1086,plain,(
% 3.23/0.81    ( ! [X4,X5] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X4,k2_xboole_0(X5,X4))) )),
% 3.23/0.81    inference(superposition,[],[f79,f721])).
% 3.23/0.81  fof(f721,plain,(
% 3.23/0.81    ( ! [X2,X3] : (k1_xboole_0 = k6_subset_1(X2,k2_xboole_0(X3,X2))) )),
% 3.23/0.81    inference(resolution,[],[f88,f83])).
% 3.23/0.81  fof(f88,plain,(
% 3.23/0.81    ( ! [X6,X4,X5] : (~r1_tarski(X4,X6) | k1_xboole_0 = k6_subset_1(X4,k2_xboole_0(X5,X6))) )),
% 3.23/0.81    inference(resolution,[],[f78,f67])).
% 3.23/0.81  fof(f67,plain,(
% 3.23/0.81    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.23/0.81    inference(cnf_transformation,[],[f31])).
% 3.23/0.81  fof(f31,plain,(
% 3.23/0.81    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.23/0.81    inference(ennf_transformation,[],[f4])).
% 3.23/0.81  fof(f4,axiom,(
% 3.23/0.81    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.23/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 3.23/0.81  fof(f4002,plain,(
% 3.23/0.81    ( ! [X8] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X8)),k2_xboole_0(X8,k10_relat_1(sK1,k1_xboole_0))) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_relat_1(sK1))) )),
% 3.23/0.81    inference(subsumption_resolution,[],[f3986,f50])).
% 3.23/0.81  fof(f3986,plain,(
% 3.23/0.81    ( ! [X8] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X8)),k2_xboole_0(X8,k10_relat_1(sK1,k1_xboole_0))) | ~v1_relat_1(sK1) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_relat_1(sK1))) )),
% 3.23/0.81    inference(superposition,[],[f313,f1268])).
% 3.23/0.81  fof(f1268,plain,(
% 3.23/0.81    ( ! [X1] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1))) )),
% 3.23/0.81    inference(superposition,[],[f1265,f578])).
% 3.23/0.81  fof(f578,plain,(
% 3.23/0.81    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 3.23/0.81    inference(subsumption_resolution,[],[f577,f50])).
% 3.23/0.81  fof(f577,plain,(
% 3.23/0.81    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 3.23/0.81    inference(subsumption_resolution,[],[f576,f51])).
% 3.23/0.81  fof(f576,plain,(
% 3.23/0.81    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 3.23/0.81    inference(resolution,[],[f72,f52])).
% 3.23/0.81  fof(f52,plain,(
% 3.23/0.81    v2_funct_1(sK1)),
% 3.23/0.81    inference(cnf_transformation,[],[f44])).
% 3.23/0.81  fof(f72,plain,(
% 3.23/0.81    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.23/0.81    inference(cnf_transformation,[],[f38])).
% 3.23/0.81  fof(f38,plain,(
% 3.23/0.81    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.23/0.81    inference(flattening,[],[f37])).
% 3.23/0.81  fof(f37,plain,(
% 3.23/0.81    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.23/0.81    inference(ennf_transformation,[],[f15])).
% 3.23/0.81  fof(f15,axiom,(
% 3.23/0.81    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.23/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 3.23/0.81  fof(f1265,plain,(
% 3.23/0.81    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 3.23/0.81    inference(subsumption_resolution,[],[f1264,f50])).
% 3.23/0.81  fof(f1264,plain,(
% 3.23/0.81    ( ! [X0] : (~v1_relat_1(sK1) | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 3.23/0.81    inference(resolution,[],[f225,f51])).
% 3.23/0.81  fof(f225,plain,(
% 3.23/0.81    ( ! [X8,X7] : (~v1_funct_1(X7) | ~v1_relat_1(X7) | k1_xboole_0 = k6_subset_1(k9_relat_1(X7,k10_relat_1(X7,X8)),X8)) )),
% 3.23/0.81    inference(resolution,[],[f60,f78])).
% 3.23/0.81  fof(f60,plain,(
% 3.23/0.81    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.23/0.81    inference(cnf_transformation,[],[f28])).
% 3.23/0.81  fof(f28,plain,(
% 3.23/0.81    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.23/0.81    inference(flattening,[],[f27])).
% 3.23/0.81  fof(f27,plain,(
% 3.23/0.81    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.23/0.81    inference(ennf_transformation,[],[f17])).
% 3.23/0.81  fof(f17,axiom,(
% 3.23/0.81    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.23/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 3.23/0.81  fof(f313,plain,(
% 3.23/0.81    ( ! [X10,X11,X9] : (r1_tarski(X9,k2_xboole_0(X10,k10_relat_1(X11,k9_relat_1(X11,k6_subset_1(X9,X10))))) | ~v1_relat_1(X11) | ~r1_tarski(k6_subset_1(X9,X10),k1_relat_1(X11))) )),
% 3.23/0.81    inference(resolution,[],[f58,f82])).
% 3.23/0.81  fof(f82,plain,(
% 3.23/0.81    ( ! [X2,X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.23/0.81    inference(definition_unfolding,[],[f70,f56])).
% 3.23/0.81  fof(f70,plain,(
% 3.23/0.81    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.23/0.81    inference(cnf_transformation,[],[f34])).
% 3.23/0.81  fof(f34,plain,(
% 3.23/0.81    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.23/0.81    inference(ennf_transformation,[],[f9])).
% 3.23/0.81  fof(f9,axiom,(
% 3.23/0.81    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.23/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 3.23/0.81  fof(f58,plain,(
% 3.23/0.81    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.23/0.81    inference(cnf_transformation,[],[f25])).
% 3.23/0.81  fof(f25,plain,(
% 3.23/0.81    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.23/0.81    inference(flattening,[],[f24])).
% 3.23/0.81  fof(f24,plain,(
% 3.23/0.81    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.23/0.81    inference(ennf_transformation,[],[f18])).
% 3.23/0.81  fof(f18,axiom,(
% 3.23/0.81    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.23/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 3.23/0.81  % SZS output end Proof for theBenchmark
% 3.23/0.81  % (23897)------------------------------
% 3.23/0.81  % (23897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.23/0.81  % (23897)Termination reason: Refutation
% 3.23/0.81  
% 3.23/0.81  % (23897)Memory used [KB]: 13688
% 3.23/0.81  % (23897)Time elapsed: 0.381 s
% 3.23/0.81  % (23897)------------------------------
% 3.23/0.81  % (23897)------------------------------
% 3.23/0.82  % (23893)Time limit reached!
% 3.23/0.82  % (23893)------------------------------
% 3.23/0.82  % (23893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.23/0.82  % (23893)Termination reason: Time limit
% 3.23/0.82  
% 3.23/0.82  % (23893)Memory used [KB]: 7164
% 3.23/0.82  % (23893)Time elapsed: 0.418 s
% 3.23/0.82  % (23893)------------------------------
% 3.23/0.82  % (23893)------------------------------
% 3.23/0.83  % (23890)Success in time 0.474 s
%------------------------------------------------------------------------------
