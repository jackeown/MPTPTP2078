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
% DateTime   : Thu Dec  3 12:54:15 EST 2020

% Result     : Theorem 2.73s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 411 expanded)
%              Number of leaves         :   26 ( 111 expanded)
%              Depth                    :   28
%              Number of atoms          :  291 (1242 expanded)
%              Number of equality atoms :   99 ( 244 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1769,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1768,f59])).

fof(f59,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f50])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f1768,plain,(
    ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1767,f60])).

fof(f60,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f1767,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1766,f55])).

fof(f55,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f1766,plain,
    ( ~ v1_relat_1(sK2)
    | r1_tarski(sK0,sK1)
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1755,f56])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f1755,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r1_tarski(sK0,sK1)
    | ~ v2_funct_1(sK2) ),
    inference(resolution,[],[f1737,f231])).

fof(f231,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,k10_relat_1(X2,k9_relat_1(X2,X4)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r1_tarski(X3,X4)
      | ~ v2_funct_1(X2) ) ),
    inference(resolution,[],[f80,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f1737,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f1622,f57])).

fof(f57,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f1622,plain,(
    ! [X0] :
      ( ~ r1_tarski(k9_relat_1(sK2,sK0),X0)
      | r1_tarski(sK0,k10_relat_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f1609,f55])).

fof(f1609,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | r1_tarski(sK0,k10_relat_1(sK2,X0))
      | ~ r1_tarski(k9_relat_1(sK2,sK0),X0) ) ),
    inference(resolution,[],[f1605,f174])).

fof(f174,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_tarski(X6,k10_relat_1(X5,X3))
      | ~ v1_relat_1(X5)
      | r1_tarski(X6,k10_relat_1(X5,X4))
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f88,f89])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f1605,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(subsumption_resolution,[],[f1602,f298])).

fof(f298,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f283,f102])).

fof(f102,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f71,f99])).

fof(f99,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f98])).

fof(f98,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f73,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f86,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f90,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f91,f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f92,f93])).

fof(f93,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f86,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f73,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f71,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f283,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(resolution,[],[f104,f107])).

fof(f107,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f85,f100])).

fof(f100,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f74,f99])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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

fof(f1602,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(superposition,[],[f573,f1536])).

fof(f1536,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f1533,f470])).

fof(f470,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f464,f221])).

fof(f221,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),k1_relat_1(sK2)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(forward_demodulation,[],[f219,f145])).

fof(f145,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    inference(resolution,[],[f78,f55])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f219,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK2)) ),
    inference(resolution,[],[f214,f63])).

fof(f63,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f214,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK2)) = k10_relat_1(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f69,f55])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f464,plain,(
    sK0 = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f457,f65])).

fof(f65,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f457,plain,(
    k1_relat_1(k6_relat_1(sK0)) = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK2)) ),
    inference(superposition,[],[f454,f369])).

fof(f369,plain,(
    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(k1_relat_1(sK2)),sK0) ),
    inference(resolution,[],[f368,f107])).

fof(f368,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(k1_relat_1(sK2)),X0) ) ),
    inference(forward_demodulation,[],[f367,f146])).

fof(f146,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f78,f63])).

fof(f367,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_relat_1(sK2))) ) ),
    inference(subsumption_resolution,[],[f366,f63])).

fof(f366,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_relat_1(sK2))) ) ),
    inference(superposition,[],[f153,f66])).

fof(f66,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f153,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(X1),sK0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X1,k6_relat_1(k1_relat_1(sK2))) = X1 ) ),
    inference(resolution,[],[f79,f144])).

fof(f144,plain,(
    ! [X6] :
      ( r1_tarski(X6,k1_relat_1(sK2))
      | ~ r1_tarski(X6,sK0) ) ),
    inference(resolution,[],[f89,f58])).

fof(f58,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f454,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(forward_demodulation,[],[f451,f146])).

fof(f451,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(resolution,[],[f217,f63])).

fof(f217,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2) ) ),
    inference(forward_demodulation,[],[f215,f65])).

fof(f215,plain,(
    ! [X2,X1] :
      ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f69,f63])).

fof(f1533,plain,(
    k1_relat_1(k7_relat_1(sK2,sK0)) = k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f663,f1511])).

fof(f1511,plain,(
    k9_relat_1(sK2,sK0) = k2_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f1504,f479])).

fof(f479,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k9_relat_1(k7_relat_1(sK2,X0),X0) ),
    inference(resolution,[],[f259,f55])).

fof(f259,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X1),X1) ) ),
    inference(resolution,[],[f70,f107])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f1504,plain,(
    k2_relat_1(k7_relat_1(sK2,sK0)) = k9_relat_1(k7_relat_1(sK2,sK0),sK0) ),
    inference(superposition,[],[f668,f470])).

fof(f668,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(resolution,[],[f116,f55])).

fof(f116,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f68,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f663,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k10_relat_1(k7_relat_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X0))) ),
    inference(resolution,[],[f111,f55])).

fof(f111,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f67,f76])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f573,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 != k5_xboole_0(X3,k10_relat_1(k7_relat_1(sK2,X3),X4))
      | r1_tarski(X3,k10_relat_1(sK2,X4)) ) ),
    inference(superposition,[],[f105,f339])).

fof(f339,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK2,X1))) ),
    inference(resolution,[],[f106,f55])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f87,f99])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f105,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f84,f100])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n009.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 17:56:56 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.19/0.44  % (28894)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.46  % (28886)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (28881)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.50  % (28882)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.51  % (28910)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.52  % (28903)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.53  % (28902)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.54  % (28884)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.54  % (28883)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.54  % (28885)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.43/0.55  % (28904)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.55  % (28897)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.43/0.55  % (28895)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.43/0.55  % (28901)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.43/0.56  % (28887)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.76/0.56  % (28896)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.76/0.57  % (28889)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.76/0.57  % (28888)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.76/0.57  % (28908)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.76/0.57  % (28899)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.76/0.57  % (28898)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.76/0.58  % (28909)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.76/0.58  % (28905)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.76/0.58  % (28890)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.76/0.58  % (28907)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.76/0.58  % (28900)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.76/0.58  % (28906)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.76/0.59  % (28892)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.76/0.59  % (28893)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.76/0.59  % (28891)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.73/0.73  % (28887)Refutation found. Thanks to Tanya!
% 2.73/0.73  % SZS status Theorem for theBenchmark
% 2.73/0.73  % SZS output start Proof for theBenchmark
% 2.73/0.73  fof(f1769,plain,(
% 2.73/0.73    $false),
% 2.73/0.73    inference(subsumption_resolution,[],[f1768,f59])).
% 2.73/0.73  fof(f59,plain,(
% 2.73/0.73    v2_funct_1(sK2)),
% 2.73/0.73    inference(cnf_transformation,[],[f51])).
% 2.73/0.73  fof(f51,plain,(
% 2.73/0.73    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.73/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f50])).
% 2.73/0.73  fof(f50,plain,(
% 2.73/0.73    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.73/0.73    introduced(choice_axiom,[])).
% 2.73/0.73  fof(f33,plain,(
% 2.73/0.73    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.73/0.73    inference(flattening,[],[f32])).
% 2.73/0.73  fof(f32,plain,(
% 2.73/0.73    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.73/0.73    inference(ennf_transformation,[],[f30])).
% 2.73/0.73  fof(f30,negated_conjecture,(
% 2.73/0.73    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 2.73/0.73    inference(negated_conjecture,[],[f29])).
% 2.73/0.73  fof(f29,conjecture,(
% 2.73/0.73    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 2.73/0.73  fof(f1768,plain,(
% 2.73/0.73    ~v2_funct_1(sK2)),
% 2.73/0.73    inference(subsumption_resolution,[],[f1767,f60])).
% 2.73/0.73  fof(f60,plain,(
% 2.73/0.73    ~r1_tarski(sK0,sK1)),
% 2.73/0.73    inference(cnf_transformation,[],[f51])).
% 2.73/0.73  fof(f1767,plain,(
% 2.73/0.73    r1_tarski(sK0,sK1) | ~v2_funct_1(sK2)),
% 2.73/0.73    inference(subsumption_resolution,[],[f1766,f55])).
% 2.73/0.73  fof(f55,plain,(
% 2.73/0.73    v1_relat_1(sK2)),
% 2.73/0.73    inference(cnf_transformation,[],[f51])).
% 2.73/0.73  fof(f1766,plain,(
% 2.73/0.73    ~v1_relat_1(sK2) | r1_tarski(sK0,sK1) | ~v2_funct_1(sK2)),
% 2.73/0.73    inference(subsumption_resolution,[],[f1755,f56])).
% 2.73/0.73  fof(f56,plain,(
% 2.73/0.73    v1_funct_1(sK2)),
% 2.73/0.73    inference(cnf_transformation,[],[f51])).
% 2.73/0.73  fof(f1755,plain,(
% 2.73/0.73    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r1_tarski(sK0,sK1) | ~v2_funct_1(sK2)),
% 2.73/0.73    inference(resolution,[],[f1737,f231])).
% 2.73/0.73  fof(f231,plain,(
% 2.73/0.73    ( ! [X4,X2,X3] : (~r1_tarski(X3,k10_relat_1(X2,k9_relat_1(X2,X4))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | r1_tarski(X3,X4) | ~v2_funct_1(X2)) )),
% 2.73/0.73    inference(resolution,[],[f80,f89])).
% 2.73/0.73  fof(f89,plain,(
% 2.73/0.73    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f49])).
% 2.73/0.73  fof(f49,plain,(
% 2.73/0.73    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.73/0.73    inference(flattening,[],[f48])).
% 2.73/0.73  fof(f48,plain,(
% 2.73/0.73    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.73/0.73    inference(ennf_transformation,[],[f5])).
% 2.73/0.73  fof(f5,axiom,(
% 2.73/0.73    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.73/0.73  fof(f80,plain,(
% 2.73/0.73    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f44])).
% 2.73/0.73  fof(f44,plain,(
% 2.73/0.73    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.73/0.73    inference(flattening,[],[f43])).
% 2.73/0.73  fof(f43,plain,(
% 2.73/0.73    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.73/0.73    inference(ennf_transformation,[],[f28])).
% 2.73/0.73  fof(f28,axiom,(
% 2.73/0.73    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 2.73/0.73  fof(f1737,plain,(
% 2.73/0.73    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))),
% 2.73/0.73    inference(resolution,[],[f1622,f57])).
% 2.73/0.73  fof(f57,plain,(
% 2.73/0.73    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 2.73/0.73    inference(cnf_transformation,[],[f51])).
% 2.73/0.73  fof(f1622,plain,(
% 2.73/0.73    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,sK0),X0) | r1_tarski(sK0,k10_relat_1(sK2,X0))) )),
% 2.73/0.73    inference(subsumption_resolution,[],[f1609,f55])).
% 2.73/0.73  fof(f1609,plain,(
% 2.73/0.73    ( ! [X0] : (~v1_relat_1(sK2) | r1_tarski(sK0,k10_relat_1(sK2,X0)) | ~r1_tarski(k9_relat_1(sK2,sK0),X0)) )),
% 2.73/0.73    inference(resolution,[],[f1605,f174])).
% 2.73/0.73  fof(f174,plain,(
% 2.73/0.73    ( ! [X6,X4,X5,X3] : (~r1_tarski(X6,k10_relat_1(X5,X3)) | ~v1_relat_1(X5) | r1_tarski(X6,k10_relat_1(X5,X4)) | ~r1_tarski(X3,X4)) )),
% 2.73/0.73    inference(resolution,[],[f88,f89])).
% 2.73/0.73  fof(f88,plain,(
% 2.73/0.73    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f47])).
% 2.73/0.73  fof(f47,plain,(
% 2.73/0.73    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 2.73/0.73    inference(flattening,[],[f46])).
% 2.73/0.73  fof(f46,plain,(
% 2.73/0.73    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 2.73/0.73    inference(ennf_transformation,[],[f20])).
% 2.73/0.73  fof(f20,axiom,(
% 2.73/0.73    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 2.73/0.73  fof(f1605,plain,(
% 2.73/0.73    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 2.73/0.73    inference(subsumption_resolution,[],[f1602,f298])).
% 2.73/0.73  fof(f298,plain,(
% 2.73/0.73    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.73/0.73    inference(forward_demodulation,[],[f283,f102])).
% 2.73/0.73  fof(f102,plain,(
% 2.73/0.73    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.73/0.73    inference(definition_unfolding,[],[f71,f99])).
% 2.73/0.73  fof(f99,plain,(
% 2.73/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.73/0.73    inference(definition_unfolding,[],[f72,f98])).
% 2.73/0.73  fof(f98,plain,(
% 2.73/0.73    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.73/0.73    inference(definition_unfolding,[],[f73,f97])).
% 2.73/0.73  fof(f97,plain,(
% 2.73/0.73    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.73/0.73    inference(definition_unfolding,[],[f86,f96])).
% 2.73/0.73  fof(f96,plain,(
% 2.73/0.73    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.73/0.73    inference(definition_unfolding,[],[f90,f95])).
% 2.73/0.73  fof(f95,plain,(
% 2.73/0.73    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.73/0.73    inference(definition_unfolding,[],[f91,f94])).
% 2.73/0.73  fof(f94,plain,(
% 2.73/0.73    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.73/0.73    inference(definition_unfolding,[],[f92,f93])).
% 2.73/0.73  fof(f93,plain,(
% 2.73/0.73    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f14])).
% 2.73/0.73  fof(f14,axiom,(
% 2.73/0.73    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.73/0.73  fof(f92,plain,(
% 2.73/0.73    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f13])).
% 2.73/0.73  fof(f13,axiom,(
% 2.73/0.73    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.73/0.73  fof(f91,plain,(
% 2.73/0.73    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f12])).
% 2.73/0.73  fof(f12,axiom,(
% 2.73/0.73    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.73/0.73  fof(f90,plain,(
% 2.73/0.73    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f11])).
% 2.73/0.73  fof(f11,axiom,(
% 2.73/0.73    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.73/0.73  fof(f86,plain,(
% 2.73/0.73    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f10])).
% 2.73/0.73  fof(f10,axiom,(
% 2.73/0.73    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.73/0.73  fof(f73,plain,(
% 2.73/0.73    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f9])).
% 2.73/0.73  fof(f9,axiom,(
% 2.73/0.73    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.73/0.73  fof(f72,plain,(
% 2.73/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.73/0.73    inference(cnf_transformation,[],[f15])).
% 2.73/0.73  fof(f15,axiom,(
% 2.73/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.73/0.73  fof(f71,plain,(
% 2.73/0.73    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.73/0.73    inference(cnf_transformation,[],[f31])).
% 2.73/0.73  fof(f31,plain,(
% 2.73/0.73    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.73/0.73    inference(rectify,[],[f1])).
% 2.73/0.73  fof(f1,axiom,(
% 2.73/0.73    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.73/0.73  fof(f283,plain,(
% 2.73/0.73    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 2.73/0.73    inference(resolution,[],[f104,f107])).
% 2.73/0.73  fof(f107,plain,(
% 2.73/0.73    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.73/0.73    inference(equality_resolution,[],[f82])).
% 2.73/0.73  fof(f82,plain,(
% 2.73/0.73    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.73/0.73    inference(cnf_transformation,[],[f53])).
% 2.73/0.73  fof(f53,plain,(
% 2.73/0.73    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.73/0.73    inference(flattening,[],[f52])).
% 2.73/0.73  fof(f52,plain,(
% 2.73/0.73    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.73/0.73    inference(nnf_transformation,[],[f2])).
% 2.73/0.73  fof(f2,axiom,(
% 2.73/0.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.73/0.73  fof(f104,plain,(
% 2.73/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.73/0.73    inference(definition_unfolding,[],[f85,f100])).
% 2.73/0.73  fof(f100,plain,(
% 2.73/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.73/0.73    inference(definition_unfolding,[],[f74,f99])).
% 2.73/0.73  fof(f74,plain,(
% 2.73/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.73/0.73    inference(cnf_transformation,[],[f4])).
% 2.73/0.73  fof(f4,axiom,(
% 2.73/0.73    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.73/0.73  fof(f85,plain,(
% 2.73/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f54])).
% 2.73/0.73  fof(f54,plain,(
% 2.73/0.73    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.73/0.73    inference(nnf_transformation,[],[f3])).
% 2.73/0.73  fof(f3,axiom,(
% 2.73/0.73    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.73/0.73  fof(f1602,plain,(
% 2.73/0.73    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 2.73/0.73    inference(superposition,[],[f573,f1536])).
% 2.73/0.73  fof(f1536,plain,(
% 2.73/0.73    sK0 = k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK0))),
% 2.73/0.73    inference(forward_demodulation,[],[f1533,f470])).
% 2.73/0.73  fof(f470,plain,(
% 2.73/0.73    sK0 = k1_relat_1(k7_relat_1(sK2,sK0))),
% 2.73/0.73    inference(superposition,[],[f464,f221])).
% 2.73/0.73  fof(f221,plain,(
% 2.73/0.73    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),k1_relat_1(sK2)) = k1_relat_1(k7_relat_1(sK2,X0))) )),
% 2.73/0.73    inference(forward_demodulation,[],[f219,f145])).
% 2.73/0.73  fof(f145,plain,(
% 2.73/0.73    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) )),
% 2.73/0.73    inference(resolution,[],[f78,f55])).
% 2.73/0.73  fof(f78,plain,(
% 2.73/0.73    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f40])).
% 2.73/0.73  fof(f40,plain,(
% 2.73/0.73    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.73/0.73    inference(ennf_transformation,[],[f25])).
% 2.73/0.73  fof(f25,axiom,(
% 2.73/0.73    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 2.73/0.73  fof(f219,plain,(
% 2.73/0.73    ( ! [X0] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK2))) )),
% 2.73/0.73    inference(resolution,[],[f214,f63])).
% 2.73/0.73  fof(f63,plain,(
% 2.73/0.73    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.73/0.73    inference(cnf_transformation,[],[f26])).
% 2.73/0.73  fof(f26,axiom,(
% 2.73/0.73    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.73/0.73  fof(f214,plain,(
% 2.73/0.73    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK2)) = k10_relat_1(X0,k1_relat_1(sK2))) )),
% 2.73/0.73    inference(resolution,[],[f69,f55])).
% 2.73/0.73  fof(f69,plain,(
% 2.73/0.73    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f36])).
% 2.73/0.73  fof(f36,plain,(
% 2.73/0.73    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.73/0.73    inference(ennf_transformation,[],[f21])).
% 2.73/0.73  fof(f21,axiom,(
% 2.73/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 2.73/0.73  fof(f464,plain,(
% 2.73/0.73    sK0 = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK2))),
% 2.73/0.73    inference(forward_demodulation,[],[f457,f65])).
% 2.73/0.73  fof(f65,plain,(
% 2.73/0.73    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.73/0.73    inference(cnf_transformation,[],[f22])).
% 2.73/0.73  fof(f22,axiom,(
% 2.73/0.73    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.73/0.73  fof(f457,plain,(
% 2.73/0.73    k1_relat_1(k6_relat_1(sK0)) = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK2))),
% 2.73/0.73    inference(superposition,[],[f454,f369])).
% 2.73/0.73  fof(f369,plain,(
% 2.73/0.73    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(k1_relat_1(sK2)),sK0)),
% 2.73/0.73    inference(resolution,[],[f368,f107])).
% 2.73/0.73  fof(f368,plain,(
% 2.73/0.73    ( ! [X0] : (~r1_tarski(X0,sK0) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(k1_relat_1(sK2)),X0)) )),
% 2.73/0.73    inference(forward_demodulation,[],[f367,f146])).
% 2.73/0.73  fof(f146,plain,(
% 2.73/0.73    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 2.73/0.73    inference(resolution,[],[f78,f63])).
% 2.73/0.73  fof(f367,plain,(
% 2.73/0.73    ( ! [X0] : (~r1_tarski(X0,sK0) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_relat_1(sK2)))) )),
% 2.73/0.73    inference(subsumption_resolution,[],[f366,f63])).
% 2.73/0.73  fof(f366,plain,(
% 2.73/0.73    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v1_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_relat_1(sK2)))) )),
% 2.73/0.73    inference(superposition,[],[f153,f66])).
% 2.73/0.73  fof(f66,plain,(
% 2.73/0.73    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.73/0.73    inference(cnf_transformation,[],[f22])).
% 2.73/0.73  fof(f153,plain,(
% 2.73/0.73    ( ! [X1] : (~r1_tarski(k2_relat_1(X1),sK0) | ~v1_relat_1(X1) | k5_relat_1(X1,k6_relat_1(k1_relat_1(sK2))) = X1) )),
% 2.73/0.73    inference(resolution,[],[f79,f144])).
% 2.73/0.73  fof(f144,plain,(
% 2.73/0.73    ( ! [X6] : (r1_tarski(X6,k1_relat_1(sK2)) | ~r1_tarski(X6,sK0)) )),
% 2.73/0.73    inference(resolution,[],[f89,f58])).
% 2.73/0.73  fof(f58,plain,(
% 2.73/0.73    r1_tarski(sK0,k1_relat_1(sK2))),
% 2.73/0.73    inference(cnf_transformation,[],[f51])).
% 2.73/0.73  fof(f79,plain,(
% 2.73/0.73    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f42])).
% 2.73/0.73  fof(f42,plain,(
% 2.73/0.73    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.73/0.73    inference(flattening,[],[f41])).
% 2.73/0.73  fof(f41,plain,(
% 2.73/0.73    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.73/0.73    inference(ennf_transformation,[],[f23])).
% 2.73/0.73  fof(f23,axiom,(
% 2.73/0.73    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 2.73/0.73  fof(f454,plain,(
% 2.73/0.73    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) )),
% 2.73/0.73    inference(forward_demodulation,[],[f451,f146])).
% 2.73/0.73  fof(f451,plain,(
% 2.73/0.73    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) )),
% 2.73/0.73    inference(resolution,[],[f217,f63])).
% 2.73/0.73  fof(f217,plain,(
% 2.73/0.73    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2)) )),
% 2.73/0.73    inference(forward_demodulation,[],[f215,f65])).
% 2.73/0.73  fof(f215,plain,(
% 2.73/0.73    ( ! [X2,X1] : (k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(X1)) )),
% 2.73/0.73    inference(resolution,[],[f69,f63])).
% 2.73/0.73  fof(f1533,plain,(
% 2.73/0.73    k1_relat_1(k7_relat_1(sK2,sK0)) = k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK0))),
% 2.73/0.73    inference(superposition,[],[f663,f1511])).
% 2.73/0.73  fof(f1511,plain,(
% 2.73/0.73    k9_relat_1(sK2,sK0) = k2_relat_1(k7_relat_1(sK2,sK0))),
% 2.73/0.73    inference(forward_demodulation,[],[f1504,f479])).
% 2.73/0.73  fof(f479,plain,(
% 2.73/0.73    ( ! [X0] : (k9_relat_1(sK2,X0) = k9_relat_1(k7_relat_1(sK2,X0),X0)) )),
% 2.73/0.73    inference(resolution,[],[f259,f55])).
% 2.73/0.73  fof(f259,plain,(
% 2.73/0.73    ( ! [X0,X1] : (~v1_relat_1(X0) | k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X1),X1)) )),
% 2.73/0.73    inference(resolution,[],[f70,f107])).
% 2.73/0.73  fof(f70,plain,(
% 2.73/0.73    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f37])).
% 2.73/0.73  fof(f37,plain,(
% 2.73/0.73    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 2.73/0.73    inference(ennf_transformation,[],[f18])).
% 2.73/0.73  fof(f18,axiom,(
% 2.73/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 2.73/0.73  fof(f1504,plain,(
% 2.73/0.73    k2_relat_1(k7_relat_1(sK2,sK0)) = k9_relat_1(k7_relat_1(sK2,sK0),sK0)),
% 2.73/0.73    inference(superposition,[],[f668,f470])).
% 2.73/0.73  fof(f668,plain,(
% 2.73/0.73    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0)))) )),
% 2.73/0.73    inference(resolution,[],[f116,f55])).
% 2.73/0.73  fof(f116,plain,(
% 2.73/0.73    ( ! [X2,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2)))) )),
% 2.73/0.73    inference(resolution,[],[f68,f76])).
% 2.73/0.73  fof(f76,plain,(
% 2.73/0.73    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f38])).
% 2.73/0.73  fof(f38,plain,(
% 2.73/0.73    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.73/0.73    inference(ennf_transformation,[],[f16])).
% 2.73/0.73  fof(f16,axiom,(
% 2.73/0.73    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.73/0.73  fof(f68,plain,(
% 2.73/0.73    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f35])).
% 2.73/0.73  fof(f35,plain,(
% 2.73/0.73    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.73/0.73    inference(ennf_transformation,[],[f17])).
% 2.73/0.73  fof(f17,axiom,(
% 2.73/0.73    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 2.73/0.73  fof(f663,plain,(
% 2.73/0.73    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k10_relat_1(k7_relat_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X0)))) )),
% 2.73/0.73    inference(resolution,[],[f111,f55])).
% 2.73/0.73  fof(f111,plain,(
% 2.73/0.73    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)))) )),
% 2.73/0.73    inference(resolution,[],[f67,f76])).
% 2.73/0.73  fof(f67,plain,(
% 2.73/0.73    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 2.73/0.73    inference(cnf_transformation,[],[f34])).
% 2.73/0.73  fof(f34,plain,(
% 2.73/0.73    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.73/0.73    inference(ennf_transformation,[],[f19])).
% 2.73/0.73  fof(f19,axiom,(
% 2.73/0.73    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 2.73/0.73  fof(f573,plain,(
% 2.73/0.73    ( ! [X4,X3] : (k1_xboole_0 != k5_xboole_0(X3,k10_relat_1(k7_relat_1(sK2,X3),X4)) | r1_tarski(X3,k10_relat_1(sK2,X4))) )),
% 2.73/0.73    inference(superposition,[],[f105,f339])).
% 2.73/0.73  fof(f339,plain,(
% 2.73/0.73    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK2,X1)))) )),
% 2.73/0.73    inference(resolution,[],[f106,f55])).
% 2.73/0.73  fof(f106,plain,(
% 2.73/0.73    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 2.73/0.73    inference(definition_unfolding,[],[f87,f99])).
% 2.73/0.73  fof(f87,plain,(
% 2.73/0.73    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f45])).
% 2.73/0.73  fof(f45,plain,(
% 2.73/0.73    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.73/0.73    inference(ennf_transformation,[],[f27])).
% 2.73/0.73  fof(f27,axiom,(
% 2.73/0.73    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 2.73/0.73  fof(f105,plain,(
% 2.73/0.73    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r1_tarski(X0,X1)) )),
% 2.73/0.73    inference(definition_unfolding,[],[f84,f100])).
% 2.73/0.73  fof(f84,plain,(
% 2.73/0.73    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.73/0.73    inference(cnf_transformation,[],[f54])).
% 2.73/0.73  % SZS output end Proof for theBenchmark
% 2.73/0.73  % (28887)------------------------------
% 2.73/0.73  % (28887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.73/0.73  % (28887)Termination reason: Refutation
% 2.73/0.73  
% 2.73/0.73  % (28887)Memory used [KB]: 12665
% 2.73/0.73  % (28887)Time elapsed: 0.326 s
% 2.73/0.73  % (28887)------------------------------
% 2.73/0.73  % (28887)------------------------------
% 3.04/0.73  % (28880)Success in time 0.394 s
%------------------------------------------------------------------------------
