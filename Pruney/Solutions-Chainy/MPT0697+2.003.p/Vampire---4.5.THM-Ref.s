%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:06 EST 2020

% Result     : Theorem 2.01s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 246 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  193 ( 756 expanded)
%              Number of equality atoms :   48 (  73 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2013,plain,(
    $false ),
    inference(resolution,[],[f1993,f139])).

fof(f139,plain,(
    ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f44,f91,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f91,plain,(
    k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f43,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f43,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f35])).

fof(f35,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1993,plain,(
    ! [X2] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1992,f827])).

fof(f827,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(superposition,[],[f725,f64])).

fof(f64,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f725,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,X0)) ),
    inference(superposition,[],[f445,f78])).

fof(f78,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f41,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f445,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X0)) ),
    inference(backward_demodulation,[],[f437,f444])).

fof(f444,plain,(
    ! [X1] : k10_relat_1(sK1,X1) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X1))) ),
    inference(subsumption_resolution,[],[f440,f418])).

fof(f418,plain,(
    ! [X11] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X11))),k10_relat_1(sK1,X11)) ),
    inference(superposition,[],[f180,f96])).

fof(f96,plain,(
    ! [X0] : k2_xboole_0(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f79,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f79,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f40,f41,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f180,plain,(
    ! [X8,X9] : r1_tarski(k10_relat_1(sK1,X8),k10_relat_1(sK1,k2_xboole_0(X8,X9))) ),
    inference(superposition,[],[f46,f71])).

fof(f71,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(unit_resulting_resolution,[],[f40,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f440,plain,(
    ! [X1] :
      ( k10_relat_1(sK1,X1) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X1)))
      | ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X1))),k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f84,f56])).

fof(f84,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) ),
    inference(unit_resulting_resolution,[],[f40,f75,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f75,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f40,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f437,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) ),
    inference(unit_resulting_resolution,[],[f84,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f47])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1992,plain,(
    ! [X2] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2),k10_relat_1(sK1,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1971,f555])).

fof(f555,plain,(
    ! [X4,X3] : r1_tarski(k10_relat_1(sK1,X4),k2_xboole_0(X3,k1_relat_1(sK1))) ),
    inference(superposition,[],[f531,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f531,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(sK1,X0),k2_xboole_0(k1_relat_1(sK1),X1)) ),
    inference(unit_resulting_resolution,[],[f46,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK1),X1)
      | r1_tarski(k10_relat_1(sK1,X0),X1) ) ),
    inference(superposition,[],[f61,f86])).

fof(f86,plain,(
    ! [X0] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f75,f52])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f1971,plain,(
    ! [X2] :
      ( r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2),k10_relat_1(sK1,k1_xboole_0))
      | ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X2)),k2_xboole_0(X2,k1_relat_1(sK1))) ) ),
    inference(superposition,[],[f157,f234])).

fof(f234,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) ),
    inference(superposition,[],[f93,f82])).

fof(f82,plain,(
    ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f42,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f42,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f79,f66])).

fof(f157,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),k10_relat_1(sK1,k9_relat_1(sK1,k6_subset_1(X0,X1))))
      | ~ r1_tarski(X0,k2_xboole_0(X1,k1_relat_1(sK1))) ) ),
    inference(resolution,[],[f77,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f60,f47])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f77,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_relat_1(sK1))
      | r1_tarski(X2,k10_relat_1(sK1,k9_relat_1(sK1,X2))) ) ),
    inference(resolution,[],[f40,f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:26:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (13761)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.50  % (13769)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.51  % (13750)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (13751)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (13747)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (13749)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (13760)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (13748)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (13757)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (13755)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (13766)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (13759)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (13752)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (13778)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (13765)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (13770)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (13764)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (13762)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (13764)Refutation not found, incomplete strategy% (13764)------------------------------
% 0.22/0.54  % (13764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13764)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13764)Memory used [KB]: 10618
% 0.22/0.54  % (13764)Time elapsed: 0.129 s
% 0.22/0.54  % (13764)------------------------------
% 0.22/0.54  % (13764)------------------------------
% 0.22/0.54  % (13774)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (13773)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (13775)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (13771)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (13767)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (13753)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (13756)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (13757)Refutation not found, incomplete strategy% (13757)------------------------------
% 0.22/0.55  % (13757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (13757)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (13757)Memory used [KB]: 10618
% 0.22/0.55  % (13757)Time elapsed: 0.144 s
% 0.22/0.55  % (13757)------------------------------
% 0.22/0.55  % (13757)------------------------------
% 0.22/0.55  % (13776)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (13776)Refutation not found, incomplete strategy% (13776)------------------------------
% 0.22/0.55  % (13776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (13776)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (13776)Memory used [KB]: 10746
% 0.22/0.55  % (13776)Time elapsed: 0.141 s
% 0.22/0.55  % (13776)------------------------------
% 0.22/0.55  % (13776)------------------------------
% 0.22/0.55  % (13763)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.48/0.55  % (13768)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.48/0.55  % (13772)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.48/0.56  % (13754)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 2.01/0.64  % (13759)Refutation found. Thanks to Tanya!
% 2.01/0.64  % SZS status Theorem for theBenchmark
% 2.01/0.64  % SZS output start Proof for theBenchmark
% 2.01/0.64  fof(f2013,plain,(
% 2.01/0.64    $false),
% 2.01/0.64    inference(resolution,[],[f1993,f139])).
% 2.01/0.64  fof(f139,plain,(
% 2.01/0.64    ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k1_xboole_0)),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f44,f91,f56])).
% 2.01/0.64  fof(f56,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f38])).
% 2.01/0.64  fof(f38,plain,(
% 2.01/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.01/0.64    inference(flattening,[],[f37])).
% 2.01/0.64  fof(f37,plain,(
% 2.01/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.01/0.64    inference(nnf_transformation,[],[f2])).
% 2.01/0.64  fof(f2,axiom,(
% 2.01/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.01/0.64  fof(f91,plain,(
% 2.01/0.64    k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f43,f67])).
% 2.01/0.64  fof(f67,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 2.01/0.64    inference(definition_unfolding,[],[f57,f47])).
% 2.01/0.64  fof(f47,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f11])).
% 2.01/0.64  fof(f11,axiom,(
% 2.01/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.01/0.64  fof(f57,plain,(
% 2.01/0.64    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.01/0.64    inference(cnf_transformation,[],[f39])).
% 2.01/0.64  fof(f39,plain,(
% 2.01/0.64    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.01/0.64    inference(nnf_transformation,[],[f3])).
% 2.01/0.64  fof(f3,axiom,(
% 2.01/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.01/0.64  fof(f43,plain,(
% 2.01/0.64    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.01/0.64    inference(cnf_transformation,[],[f36])).
% 2.01/0.64  fof(f36,plain,(
% 2.01/0.64    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 2.01/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f35])).
% 2.01/0.64  fof(f35,plain,(
% 2.01/0.64    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.01/0.64    introduced(choice_axiom,[])).
% 2.01/0.64  fof(f21,plain,(
% 2.01/0.64    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.01/0.64    inference(flattening,[],[f20])).
% 2.01/0.64  fof(f20,plain,(
% 2.01/0.64    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.01/0.64    inference(ennf_transformation,[],[f19])).
% 2.01/0.64  fof(f19,negated_conjecture,(
% 2.01/0.64    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.01/0.64    inference(negated_conjecture,[],[f18])).
% 2.01/0.64  fof(f18,conjecture,(
% 2.01/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 2.01/0.64  fof(f44,plain,(
% 2.01/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f6])).
% 2.01/0.64  fof(f6,axiom,(
% 2.01/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.01/0.64  fof(f1993,plain,(
% 2.01/0.64    ( ! [X2] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2),k1_xboole_0)) )),
% 2.01/0.64    inference(forward_demodulation,[],[f1992,f827])).
% 2.01/0.64  fof(f827,plain,(
% 2.01/0.64    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 2.01/0.64    inference(superposition,[],[f725,f64])).
% 2.01/0.64  fof(f64,plain,(
% 2.01/0.64    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 2.01/0.64    inference(definition_unfolding,[],[f45,f47])).
% 2.01/0.64  fof(f45,plain,(
% 2.01/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.01/0.64    inference(cnf_transformation,[],[f8])).
% 2.01/0.64  fof(f8,axiom,(
% 2.01/0.64    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.01/0.64  fof(f725,plain,(
% 2.01/0.64    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,X0))) )),
% 2.01/0.64    inference(superposition,[],[f445,f78])).
% 2.01/0.64  fof(f78,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f40,f41,f62])).
% 2.01/0.64  fof(f62,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f32])).
% 2.01/0.64  fof(f32,plain,(
% 2.01/0.64    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.01/0.64    inference(flattening,[],[f31])).
% 2.01/0.64  fof(f31,plain,(
% 2.01/0.64    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.01/0.64    inference(ennf_transformation,[],[f15])).
% 2.01/0.64  fof(f15,axiom,(
% 2.01/0.64    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 2.01/0.64  fof(f41,plain,(
% 2.01/0.64    v1_funct_1(sK1)),
% 2.01/0.64    inference(cnf_transformation,[],[f36])).
% 2.01/0.64  fof(f40,plain,(
% 2.01/0.64    v1_relat_1(sK1)),
% 2.01/0.64    inference(cnf_transformation,[],[f36])).
% 2.01/0.64  fof(f445,plain,(
% 2.01/0.64    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X0))) )),
% 2.01/0.64    inference(backward_demodulation,[],[f437,f444])).
% 2.01/0.64  fof(f444,plain,(
% 2.01/0.64    ( ! [X1] : (k10_relat_1(sK1,X1) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X1)))) )),
% 2.01/0.64    inference(subsumption_resolution,[],[f440,f418])).
% 2.01/0.64  fof(f418,plain,(
% 2.01/0.64    ( ! [X11] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X11))),k10_relat_1(sK1,X11))) )),
% 2.01/0.64    inference(superposition,[],[f180,f96])).
% 2.01/0.64  fof(f96,plain,(
% 2.01/0.64    ( ! [X0] : (k2_xboole_0(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) = X0) )),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f79,f52])).
% 2.01/0.64  fof(f52,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.01/0.64    inference(cnf_transformation,[],[f25])).
% 2.01/0.64  fof(f25,plain,(
% 2.01/0.64    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.01/0.64    inference(ennf_transformation,[],[f5])).
% 2.01/0.64  fof(f5,axiom,(
% 2.01/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.01/0.64  fof(f79,plain,(
% 2.01/0.64    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f40,f41,f53])).
% 2.01/0.64  fof(f53,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f27])).
% 2.01/0.64  fof(f27,plain,(
% 2.01/0.64    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(flattening,[],[f26])).
% 2.01/0.64  fof(f26,plain,(
% 2.01/0.64    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.01/0.64    inference(ennf_transformation,[],[f16])).
% 2.01/0.64  fof(f16,axiom,(
% 2.01/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 2.01/0.64  fof(f180,plain,(
% 2.01/0.64    ( ! [X8,X9] : (r1_tarski(k10_relat_1(sK1,X8),k10_relat_1(sK1,k2_xboole_0(X8,X9)))) )),
% 2.01/0.64    inference(superposition,[],[f46,f71])).
% 2.01/0.64  fof(f71,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k10_relat_1(sK1,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f40,f59])).
% 2.01/0.64  fof(f59,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f28])).
% 2.01/0.64  fof(f28,plain,(
% 2.01/0.64    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.01/0.64    inference(ennf_transformation,[],[f13])).
% 2.01/0.64  fof(f13,axiom,(
% 2.01/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).
% 2.01/0.64  fof(f46,plain,(
% 2.01/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f10])).
% 2.01/0.64  fof(f10,axiom,(
% 2.01/0.64    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.01/0.64  fof(f440,plain,(
% 2.01/0.64    ( ! [X1] : (k10_relat_1(sK1,X1) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X1))) | ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X1))),k10_relat_1(sK1,X1))) )),
% 2.01/0.64    inference(resolution,[],[f84,f56])).
% 2.01/0.64  fof(f84,plain,(
% 2.01/0.64    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) )),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f40,f75,f51])).
% 2.01/0.64  fof(f51,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f24])).
% 2.01/0.64  fof(f24,plain,(
% 2.01/0.64    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(flattening,[],[f23])).
% 2.01/0.64  fof(f23,plain,(
% 2.01/0.64    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(ennf_transformation,[],[f17])).
% 2.01/0.64  fof(f17,axiom,(
% 2.01/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 2.01/0.64  fof(f75,plain,(
% 2.01/0.64    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f40,f50])).
% 2.01/0.64  fof(f50,plain,(
% 2.01/0.64    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f22])).
% 2.01/0.64  fof(f22,plain,(
% 2.01/0.64    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(ennf_transformation,[],[f12])).
% 2.01/0.64  fof(f12,axiom,(
% 2.01/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 2.01/0.64  fof(f437,plain,(
% 2.01/0.64    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) )),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f84,f66])).
% 2.01/0.64  fof(f66,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 2.01/0.64    inference(definition_unfolding,[],[f58,f47])).
% 2.01/0.64  fof(f58,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f39])).
% 2.01/0.64  fof(f1992,plain,(
% 2.01/0.64    ( ! [X2] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2),k10_relat_1(sK1,k1_xboole_0))) )),
% 2.01/0.64    inference(subsumption_resolution,[],[f1971,f555])).
% 2.01/0.64  fof(f555,plain,(
% 2.01/0.64    ( ! [X4,X3] : (r1_tarski(k10_relat_1(sK1,X4),k2_xboole_0(X3,k1_relat_1(sK1)))) )),
% 2.01/0.64    inference(superposition,[],[f531,f48])).
% 2.01/0.64  fof(f48,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f1])).
% 2.01/0.64  fof(f1,axiom,(
% 2.01/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.01/0.64  fof(f531,plain,(
% 2.01/0.64    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK1,X0),k2_xboole_0(k1_relat_1(sK1),X1))) )),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f46,f143])).
% 2.01/0.64  fof(f143,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK1),X1) | r1_tarski(k10_relat_1(sK1,X0),X1)) )),
% 2.01/0.64    inference(superposition,[],[f61,f86])).
% 2.01/0.64  fof(f86,plain,(
% 2.01/0.64    ( ! [X0] : (k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f75,f52])).
% 2.01/0.64  fof(f61,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f30])).
% 2.01/0.64  fof(f30,plain,(
% 2.01/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.01/0.64    inference(ennf_transformation,[],[f4])).
% 2.01/0.64  fof(f4,axiom,(
% 2.01/0.64    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.01/0.64  fof(f1971,plain,(
% 2.01/0.64    ( ! [X2] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2),k10_relat_1(sK1,k1_xboole_0)) | ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X2)),k2_xboole_0(X2,k1_relat_1(sK1)))) )),
% 2.01/0.64    inference(superposition,[],[f157,f234])).
% 2.01/0.64  fof(f234,plain,(
% 2.01/0.64    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))) )),
% 2.01/0.64    inference(superposition,[],[f93,f82])).
% 2.01/0.64  fof(f82,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f40,f41,f42,f63])).
% 2.01/0.64  fof(f63,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f34])).
% 2.01/0.64  fof(f34,plain,(
% 2.01/0.64    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.01/0.64    inference(flattening,[],[f33])).
% 2.01/0.64  fof(f33,plain,(
% 2.01/0.64    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.01/0.64    inference(ennf_transformation,[],[f14])).
% 2.01/0.64  fof(f14,axiom,(
% 2.01/0.64    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 2.01/0.64  fof(f42,plain,(
% 2.01/0.64    v2_funct_1(sK1)),
% 2.01/0.64    inference(cnf_transformation,[],[f36])).
% 2.01/0.64  fof(f93,plain,(
% 2.01/0.64    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f79,f66])).
% 2.01/0.64  fof(f157,plain,(
% 2.01/0.64    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),k10_relat_1(sK1,k9_relat_1(sK1,k6_subset_1(X0,X1)))) | ~r1_tarski(X0,k2_xboole_0(X1,k1_relat_1(sK1)))) )),
% 2.01/0.64    inference(resolution,[],[f77,f68])).
% 2.01/0.64  fof(f68,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.01/0.64    inference(definition_unfolding,[],[f60,f47])).
% 2.01/0.64  fof(f60,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f29])).
% 2.01/0.64  fof(f29,plain,(
% 2.01/0.64    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.01/0.64    inference(ennf_transformation,[],[f9])).
% 2.01/0.64  fof(f9,axiom,(
% 2.01/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.01/0.64  fof(f77,plain,(
% 2.01/0.64    ( ! [X2] : (~r1_tarski(X2,k1_relat_1(sK1)) | r1_tarski(X2,k10_relat_1(sK1,k9_relat_1(sK1,X2)))) )),
% 2.01/0.64    inference(resolution,[],[f40,f51])).
% 2.01/0.64  % SZS output end Proof for theBenchmark
% 2.01/0.64  % (13759)------------------------------
% 2.01/0.64  % (13759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.64  % (13759)Termination reason: Refutation
% 2.01/0.64  
% 2.01/0.64  % (13759)Memory used [KB]: 7547
% 2.01/0.64  % (13759)Time elapsed: 0.238 s
% 2.01/0.64  % (13759)------------------------------
% 2.01/0.64  % (13759)------------------------------
% 2.01/0.64  % (13746)Success in time 0.279 s
%------------------------------------------------------------------------------
