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
% DateTime   : Thu Dec  3 12:53:51 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 381 expanded)
%              Number of leaves         :   27 ( 105 expanded)
%              Depth                    :   20
%              Number of atoms          :  267 ( 948 expanded)
%              Number of equality atoms :  109 ( 283 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f824,plain,(
    $false ),
    inference(subsumption_resolution,[],[f823,f57])).

fof(f57,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f48])).

fof(f48,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f823,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f819,f194])).

fof(f194,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f193,f102])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f193,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f99,f98])).

fof(f98,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f65,f96])).

fof(f96,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f95])).

fof(f95,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f79,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f87,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f88,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f89,f90])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f65,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f78,f97])).

fof(f97,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f69,f96])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f819,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f314,f603])).

fof(f603,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f602,f568])).

fof(f568,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f561,f55])).

fof(f55,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f561,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f528,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f528,plain,(
    sK0 = k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(superposition,[],[f513,f144])).

fof(f144,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f139,f58])).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f139,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f63,f55])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f513,plain,(
    sK0 = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(superposition,[],[f402,f252])).

fof(f252,plain,(
    k1_relat_1(sK1) = k2_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f187,f56])).

fof(f56,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f187,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k2_xboole_0(X2,X3) = X3 ) ),
    inference(subsumption_resolution,[],[f184,f102])).

fof(f184,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X2,X3)
      | k2_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f86,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK2(X0,X1,X2))
      | k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK2(X0,X1,X2))
        & r1_tarski(X2,sK2(X0,X1,X2))
        & r1_tarski(X0,sK2(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK2(X0,X1,X2))
        & r1_tarski(X2,sK2(X0,X1,X2))
        & r1_tarski(X0,sK2(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK2(X0,X1,X2))
      | k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f402,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f390,f209])).

fof(f209,plain,(
    ! [X21,X22] : k2_xboole_0(X21,k10_relat_1(k6_relat_1(X21),X22)) = X21 ),
    inference(resolution,[],[f186,f105])).

fof(f105,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f104,f58])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f71,f59])).

fof(f59,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k2_xboole_0(X0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f185,f102])).

fof(f185,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0)
      | k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f86,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,sK2(X0,X1,X2))
      | k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f390,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f154,f111])).

fof(f111,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f110,f59])).

fof(f110,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f108,f60])).

fof(f60,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f108,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f61,f58])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f154,plain,(
    ! [X4,X2,X3] : k10_relat_1(k6_relat_1(X2),k2_xboole_0(X3,X4)) = k2_xboole_0(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),X4)) ),
    inference(resolution,[],[f81,f58])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f602,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f601,f55])).

fof(f601,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f109,f596])).

fof(f596,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f321,f568])).

fof(f321,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f151,f55])).

fof(f151,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4))) ) ),
    inference(subsumption_resolution,[],[f150,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f150,plain,(
    ! [X4,X3] :
      ( k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k7_relat_1(X3,X4)) ) ),
    inference(subsumption_resolution,[],[f148,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f148,plain,(
    ! [X4,X3] :
      ( k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k7_relat_1(X3,X4)) ) ),
    inference(superposition,[],[f64,f62])).

fof(f62,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f109,plain,(
    ! [X2,X1] :
      ( k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f61,f70])).

fof(f314,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k5_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X1),X2))
      | r1_tarski(X1,k10_relat_1(sK1,X2)) ) ),
    inference(superposition,[],[f100,f212])).

fof(f212,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK1,X1))) ),
    inference(resolution,[],[f101,f55])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f80,f96])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f97])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (29912)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.50  % (29928)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.50  % (29907)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.50  % (29920)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (29904)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (29903)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (29910)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (29905)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (29926)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (29925)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (29915)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (29908)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (29906)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (29917)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (29918)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (29929)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (29931)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (29932)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (29921)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (29909)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (29927)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (29931)Refutation not found, incomplete strategy% (29931)------------------------------
% 0.20/0.54  % (29931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29931)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29931)Memory used [KB]: 10746
% 0.20/0.54  % (29931)Time elapsed: 0.142 s
% 0.20/0.54  % (29931)------------------------------
% 0.20/0.54  % (29931)------------------------------
% 0.20/0.54  % (29930)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (29923)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (29919)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (29919)Refutation not found, incomplete strategy% (29919)------------------------------
% 0.20/0.54  % (29919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29919)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29919)Memory used [KB]: 10618
% 0.20/0.54  % (29919)Time elapsed: 0.139 s
% 0.20/0.54  % (29919)------------------------------
% 0.20/0.54  % (29919)------------------------------
% 0.20/0.54  % (29916)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (29913)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (29922)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (29911)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (29913)Refutation not found, incomplete strategy% (29913)------------------------------
% 0.20/0.54  % (29913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29913)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29913)Memory used [KB]: 10746
% 0.20/0.54  % (29913)Time elapsed: 0.140 s
% 0.20/0.54  % (29913)------------------------------
% 0.20/0.54  % (29913)------------------------------
% 0.20/0.55  % (29924)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (29914)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.96/0.61  % (29925)Refutation found. Thanks to Tanya!
% 1.96/0.61  % SZS status Theorem for theBenchmark
% 1.96/0.61  % SZS output start Proof for theBenchmark
% 1.96/0.61  fof(f824,plain,(
% 1.96/0.61    $false),
% 1.96/0.61    inference(subsumption_resolution,[],[f823,f57])).
% 1.96/0.61  fof(f57,plain,(
% 1.96/0.61    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.96/0.61    inference(cnf_transformation,[],[f49])).
% 1.96/0.61  fof(f49,plain,(
% 1.96/0.61    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.96/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f48])).
% 1.96/0.61  fof(f48,plain,(
% 1.96/0.61    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.96/0.61    introduced(choice_axiom,[])).
% 1.96/0.61  fof(f32,plain,(
% 1.96/0.61    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.96/0.61    inference(flattening,[],[f31])).
% 1.96/0.61  fof(f31,plain,(
% 1.96/0.61    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.96/0.61    inference(ennf_transformation,[],[f29])).
% 1.96/0.61  fof(f29,negated_conjecture,(
% 1.96/0.61    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.96/0.61    inference(negated_conjecture,[],[f28])).
% 1.96/0.61  fof(f28,conjecture,(
% 1.96/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.96/0.61  fof(f823,plain,(
% 1.96/0.61    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.96/0.61    inference(subsumption_resolution,[],[f819,f194])).
% 1.96/0.61  fof(f194,plain,(
% 1.96/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.96/0.61    inference(subsumption_resolution,[],[f193,f102])).
% 1.96/0.61  fof(f102,plain,(
% 1.96/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.96/0.61    inference(equality_resolution,[],[f75])).
% 1.96/0.61  fof(f75,plain,(
% 1.96/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.96/0.61    inference(cnf_transformation,[],[f51])).
% 1.96/0.61  fof(f51,plain,(
% 1.96/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.96/0.61    inference(flattening,[],[f50])).
% 1.96/0.61  fof(f50,plain,(
% 1.96/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.96/0.61    inference(nnf_transformation,[],[f2])).
% 1.96/0.61  fof(f2,axiom,(
% 1.96/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.96/0.61  fof(f193,plain,(
% 1.96/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X0)) )),
% 1.96/0.61    inference(superposition,[],[f99,f98])).
% 1.96/0.61  fof(f98,plain,(
% 1.96/0.61    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.96/0.61    inference(definition_unfolding,[],[f65,f96])).
% 1.96/0.61  fof(f96,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.96/0.61    inference(definition_unfolding,[],[f67,f95])).
% 1.96/0.61  fof(f95,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.96/0.61    inference(definition_unfolding,[],[f68,f94])).
% 1.96/0.61  fof(f94,plain,(
% 1.96/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.96/0.61    inference(definition_unfolding,[],[f79,f93])).
% 1.96/0.61  fof(f93,plain,(
% 1.96/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.96/0.61    inference(definition_unfolding,[],[f87,f92])).
% 1.96/0.61  fof(f92,plain,(
% 1.96/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.96/0.61    inference(definition_unfolding,[],[f88,f91])).
% 1.96/0.61  fof(f91,plain,(
% 1.96/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.96/0.61    inference(definition_unfolding,[],[f89,f90])).
% 1.96/0.61  fof(f90,plain,(
% 1.96/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f14])).
% 1.96/0.61  fof(f14,axiom,(
% 1.96/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.96/0.61  fof(f89,plain,(
% 1.96/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f13])).
% 1.96/0.61  fof(f13,axiom,(
% 1.96/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.96/0.61  fof(f88,plain,(
% 1.96/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f12])).
% 1.96/0.61  fof(f12,axiom,(
% 1.96/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.96/0.61  fof(f87,plain,(
% 1.96/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f11])).
% 1.96/0.61  fof(f11,axiom,(
% 1.96/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.96/0.61  fof(f79,plain,(
% 1.96/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f10])).
% 1.96/0.61  fof(f10,axiom,(
% 1.96/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.96/0.61  fof(f68,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f9])).
% 1.96/0.61  fof(f9,axiom,(
% 1.96/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.96/0.61  fof(f67,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.96/0.61    inference(cnf_transformation,[],[f15])).
% 1.96/0.61  fof(f15,axiom,(
% 1.96/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.96/0.61  fof(f65,plain,(
% 1.96/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.96/0.61    inference(cnf_transformation,[],[f30])).
% 1.96/0.61  fof(f30,plain,(
% 1.96/0.61    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.96/0.61    inference(rectify,[],[f1])).
% 1.96/0.61  fof(f1,axiom,(
% 1.96/0.61    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.96/0.61  fof(f99,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r1_tarski(X0,X1)) )),
% 1.96/0.61    inference(definition_unfolding,[],[f78,f97])).
% 1.96/0.61  fof(f97,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.96/0.61    inference(definition_unfolding,[],[f69,f96])).
% 1.96/0.61  fof(f69,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.96/0.61    inference(cnf_transformation,[],[f4])).
% 1.96/0.61  fof(f4,axiom,(
% 1.96/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.96/0.61  fof(f78,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f52])).
% 1.96/0.61  fof(f52,plain,(
% 1.96/0.61    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.96/0.61    inference(nnf_transformation,[],[f3])).
% 1.96/0.61  fof(f3,axiom,(
% 1.96/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.96/0.61  fof(f819,plain,(
% 1.96/0.61    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.96/0.61    inference(superposition,[],[f314,f603])).
% 1.96/0.61  fof(f603,plain,(
% 1.96/0.61    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 1.96/0.61    inference(forward_demodulation,[],[f602,f568])).
% 1.96/0.61  fof(f568,plain,(
% 1.96/0.61    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.96/0.61    inference(subsumption_resolution,[],[f561,f55])).
% 1.96/0.61  fof(f55,plain,(
% 1.96/0.61    v1_relat_1(sK1)),
% 1.96/0.61    inference(cnf_transformation,[],[f49])).
% 1.96/0.61  fof(f561,plain,(
% 1.96/0.61    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 1.96/0.61    inference(superposition,[],[f528,f73])).
% 1.96/0.61  fof(f73,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f40])).
% 1.96/0.61  fof(f40,plain,(
% 1.96/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.96/0.61    inference(ennf_transformation,[],[f26])).
% 1.96/0.61  fof(f26,axiom,(
% 1.96/0.61    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.96/0.61  fof(f528,plain,(
% 1.96/0.61    sK0 = k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),
% 1.96/0.61    inference(superposition,[],[f513,f144])).
% 1.96/0.61  fof(f144,plain,(
% 1.96/0.61    ( ! [X0] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) )),
% 1.96/0.61    inference(resolution,[],[f139,f58])).
% 1.96/0.61  fof(f58,plain,(
% 1.96/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.96/0.61    inference(cnf_transformation,[],[f16])).
% 1.96/0.61  fof(f16,axiom,(
% 1.96/0.61    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.96/0.61  fof(f139,plain,(
% 1.96/0.61    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1))) )),
% 1.96/0.61    inference(resolution,[],[f63,f55])).
% 1.96/0.61  fof(f63,plain,(
% 1.96/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f35])).
% 1.96/0.61  fof(f35,plain,(
% 1.96/0.61    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.96/0.61    inference(ennf_transformation,[],[f23])).
% 1.96/0.61  fof(f23,axiom,(
% 1.96/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.96/0.61  fof(f513,plain,(
% 1.96/0.61    sK0 = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),
% 1.96/0.61    inference(superposition,[],[f402,f252])).
% 1.96/0.61  fof(f252,plain,(
% 1.96/0.61    k1_relat_1(sK1) = k2_xboole_0(sK0,k1_relat_1(sK1))),
% 1.96/0.61    inference(resolution,[],[f187,f56])).
% 1.96/0.61  fof(f56,plain,(
% 1.96/0.61    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.96/0.61    inference(cnf_transformation,[],[f49])).
% 1.96/0.61  fof(f187,plain,(
% 1.96/0.61    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k2_xboole_0(X2,X3) = X3) )),
% 1.96/0.61    inference(subsumption_resolution,[],[f184,f102])).
% 1.96/0.61  fof(f184,plain,(
% 1.96/0.61    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X2,X3)) )),
% 1.96/0.61    inference(duplicate_literal_removal,[],[f181])).
% 1.96/0.61  fof(f181,plain,(
% 1.96/0.61    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X2,X3) | k2_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X2,X3)) )),
% 1.96/0.61    inference(resolution,[],[f86,f85])).
% 1.96/0.61  fof(f85,plain,(
% 1.96/0.61    ( ! [X2,X0,X1] : (r1_tarski(X2,sK2(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f54])).
% 1.96/0.61  fof(f54,plain,(
% 1.96/0.61    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK2(X0,X1,X2)) & r1_tarski(X2,sK2(X0,X1,X2)) & r1_tarski(X0,sK2(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.96/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f53])).
% 1.96/0.61  fof(f53,plain,(
% 1.96/0.61    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK2(X0,X1,X2)) & r1_tarski(X2,sK2(X0,X1,X2)) & r1_tarski(X0,sK2(X0,X1,X2))))),
% 1.96/0.61    introduced(choice_axiom,[])).
% 1.96/0.61  fof(f47,plain,(
% 1.96/0.61    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.96/0.61    inference(flattening,[],[f46])).
% 1.96/0.61  fof(f46,plain,(
% 1.96/0.61    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.96/0.61    inference(ennf_transformation,[],[f6])).
% 1.96/0.61  fof(f6,axiom,(
% 1.96/0.61    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).
% 1.96/0.61  fof(f86,plain,(
% 1.96/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK2(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f54])).
% 1.96/0.61  fof(f402,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1)) = X0) )),
% 1.96/0.61    inference(forward_demodulation,[],[f390,f209])).
% 1.96/0.61  fof(f209,plain,(
% 1.96/0.61    ( ! [X21,X22] : (k2_xboole_0(X21,k10_relat_1(k6_relat_1(X21),X22)) = X21) )),
% 1.96/0.61    inference(resolution,[],[f186,f105])).
% 1.96/0.61  fof(f105,plain,(
% 1.96/0.61    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.96/0.61    inference(subsumption_resolution,[],[f104,f58])).
% 1.96/0.61  fof(f104,plain,(
% 1.96/0.61    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.96/0.61    inference(superposition,[],[f71,f59])).
% 1.96/0.61  fof(f59,plain,(
% 1.96/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.96/0.61    inference(cnf_transformation,[],[f24])).
% 1.96/0.61  fof(f24,axiom,(
% 1.96/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.96/0.61  fof(f71,plain,(
% 1.96/0.61    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f38])).
% 1.96/0.61  fof(f38,plain,(
% 1.96/0.61    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.96/0.61    inference(ennf_transformation,[],[f20])).
% 1.96/0.61  fof(f20,axiom,(
% 1.96/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.96/0.61  fof(f186,plain,(
% 1.96/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k2_xboole_0(X0,X1) = X0) )),
% 1.96/0.61    inference(subsumption_resolution,[],[f185,f102])).
% 1.96/0.61  fof(f185,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 1.96/0.61    inference(duplicate_literal_removal,[],[f180])).
% 1.96/0.61  fof(f180,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0) | k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 1.96/0.61    inference(resolution,[],[f86,f84])).
% 1.96/0.61  fof(f84,plain,(
% 1.96/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,sK2(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f54])).
% 1.96/0.61  fof(f390,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1))) )),
% 1.96/0.61    inference(superposition,[],[f154,f111])).
% 1.96/0.61  fof(f111,plain,(
% 1.96/0.61    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.96/0.61    inference(forward_demodulation,[],[f110,f59])).
% 1.96/0.61  fof(f110,plain,(
% 1.96/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 1.96/0.61    inference(forward_demodulation,[],[f108,f60])).
% 1.96/0.61  fof(f60,plain,(
% 1.96/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.96/0.61    inference(cnf_transformation,[],[f24])).
% 1.96/0.61  fof(f108,plain,(
% 1.96/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 1.96/0.61    inference(resolution,[],[f61,f58])).
% 1.96/0.61  fof(f61,plain,(
% 1.96/0.61    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 1.96/0.61    inference(cnf_transformation,[],[f33])).
% 1.96/0.61  fof(f33,plain,(
% 1.96/0.61    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.96/0.61    inference(ennf_transformation,[],[f21])).
% 1.96/0.61  fof(f21,axiom,(
% 1.96/0.61    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.96/0.61  fof(f154,plain,(
% 1.96/0.61    ( ! [X4,X2,X3] : (k10_relat_1(k6_relat_1(X2),k2_xboole_0(X3,X4)) = k2_xboole_0(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),X4))) )),
% 1.96/0.61    inference(resolution,[],[f81,f58])).
% 1.96/0.61  fof(f81,plain,(
% 1.96/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 1.96/0.61    inference(cnf_transformation,[],[f42])).
% 1.96/0.61  fof(f42,plain,(
% 1.96/0.61    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.96/0.61    inference(ennf_transformation,[],[f22])).
% 1.96/0.61  fof(f22,axiom,(
% 1.96/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 1.96/0.61  fof(f602,plain,(
% 1.96/0.61    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 1.96/0.61    inference(subsumption_resolution,[],[f601,f55])).
% 1.96/0.61  fof(f601,plain,(
% 1.96/0.61    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 1.96/0.61    inference(superposition,[],[f109,f596])).
% 1.96/0.61  fof(f596,plain,(
% 1.96/0.61    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 1.96/0.61    inference(superposition,[],[f321,f568])).
% 1.96/0.61  fof(f321,plain,(
% 1.96/0.61    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.96/0.61    inference(resolution,[],[f151,f55])).
% 1.96/0.61  fof(f151,plain,(
% 1.96/0.61    ( ! [X4,X3] : (~v1_relat_1(X3) | k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4)))) )),
% 1.96/0.61    inference(subsumption_resolution,[],[f150,f70])).
% 1.96/0.61  fof(f70,plain,(
% 1.96/0.61    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f37])).
% 1.96/0.61  fof(f37,plain,(
% 1.96/0.61    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.96/0.61    inference(ennf_transformation,[],[f17])).
% 1.96/0.61  fof(f17,axiom,(
% 1.96/0.61    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.96/0.61  fof(f150,plain,(
% 1.96/0.61    ( ! [X4,X3] : (k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4))) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(X3,X4))) )),
% 1.96/0.61    inference(subsumption_resolution,[],[f148,f72])).
% 1.96/0.61  fof(f72,plain,(
% 1.96/0.61    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f39])).
% 1.96/0.61  fof(f39,plain,(
% 1.96/0.61    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.96/0.61    inference(ennf_transformation,[],[f25])).
% 1.96/0.61  fof(f25,axiom,(
% 1.96/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.96/0.61  fof(f148,plain,(
% 1.96/0.61    ( ! [X4,X3] : (k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4))) | ~r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X4) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(X3,X4))) )),
% 1.96/0.61    inference(superposition,[],[f64,f62])).
% 1.96/0.61  fof(f62,plain,(
% 1.96/0.61    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f34])).
% 1.96/0.61  fof(f34,plain,(
% 1.96/0.61    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.96/0.61    inference(ennf_transformation,[],[f18])).
% 1.96/0.61  fof(f18,axiom,(
% 1.96/0.61    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.96/0.61  fof(f64,plain,(
% 1.96/0.61    ( ! [X2,X0,X1] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f36])).
% 1.96/0.61  fof(f36,plain,(
% 1.96/0.61    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 1.96/0.61    inference(ennf_transformation,[],[f19])).
% 1.96/0.61  fof(f19,axiom,(
% 1.96/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 1.96/0.61  fof(f109,plain,(
% 1.96/0.61    ( ! [X2,X1] : (k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2))) | ~v1_relat_1(X1)) )),
% 1.96/0.61    inference(resolution,[],[f61,f70])).
% 1.96/0.61  fof(f314,plain,(
% 1.96/0.61    ( ! [X2,X1] : (k1_xboole_0 != k5_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X1),X2)) | r1_tarski(X1,k10_relat_1(sK1,X2))) )),
% 1.96/0.61    inference(superposition,[],[f100,f212])).
% 1.96/0.61  fof(f212,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK1,X1)))) )),
% 1.96/0.61    inference(resolution,[],[f101,f55])).
% 1.96/0.61  fof(f101,plain,(
% 1.96/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 1.96/0.61    inference(definition_unfolding,[],[f80,f96])).
% 1.96/0.61  fof(f80,plain,(
% 1.96/0.61    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f41])).
% 1.96/0.61  fof(f41,plain,(
% 1.96/0.61    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.96/0.61    inference(ennf_transformation,[],[f27])).
% 1.96/0.61  fof(f27,axiom,(
% 1.96/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.96/0.61  fof(f100,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r1_tarski(X0,X1)) )),
% 1.96/0.61    inference(definition_unfolding,[],[f77,f97])).
% 1.96/0.61  fof(f77,plain,(
% 1.96/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.96/0.61    inference(cnf_transformation,[],[f52])).
% 1.96/0.61  % SZS output end Proof for theBenchmark
% 1.96/0.61  % (29925)------------------------------
% 1.96/0.61  % (29925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.61  % (29925)Termination reason: Refutation
% 1.96/0.61  
% 1.96/0.61  % (29925)Memory used [KB]: 7291
% 1.96/0.61  % (29925)Time elapsed: 0.168 s
% 1.96/0.61  % (29925)------------------------------
% 1.96/0.61  % (29925)------------------------------
% 1.96/0.62  % (29902)Success in time 0.262 s
%------------------------------------------------------------------------------
