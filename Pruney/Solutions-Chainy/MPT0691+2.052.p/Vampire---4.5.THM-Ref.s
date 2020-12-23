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
% DateTime   : Thu Dec  3 12:53:52 EST 2020

% Result     : Theorem 2.87s
% Output     : Refutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 470 expanded)
%              Number of leaves         :   22 ( 133 expanded)
%              Depth                    :   19
%              Number of atoms          :  177 ( 946 expanded)
%              Number of equality atoms :   79 ( 267 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3033,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3032,f137])).

fof(f137,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f132,f131])).

fof(f131,plain,(
    sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f55,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f72,f95])).

fof(f95,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f94])).

fof(f94,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f79,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f86,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f87,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f88,f89])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f55,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f47])).

fof(f47,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f132,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK1)))) ),
    inference(unit_resulting_resolution,[],[f55,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f78,f96])).

fof(f96,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f67,f95])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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

fof(f3032,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f169,f3031])).

fof(f3031,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f3030,f2746])).

fof(f2746,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f114,f2733,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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

fof(f2733,plain,(
    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f152,f2729])).

fof(f2729,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(superposition,[],[f659,f131])).

fof(f659,plain,(
    ! [X0] : k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f117,f103])).

fof(f103,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f54,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f54,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f117,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK1,X1))) ),
    inference(unit_resulting_resolution,[],[f54,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f80,f95])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f152,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f112,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f112,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f54,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f114,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f54,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f3030,plain,(
    k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f139,f2835])).

fof(f2835,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2773,f129])).

fof(f129,plain,(
    k9_relat_1(sK1,sK0) = k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f54,f55,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f2773,plain,(
    k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(backward_demodulation,[],[f373,f2746])).

fof(f373,plain,(
    k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,sK0))) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f360,f193])).

fof(f193,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f183,f140])).

fof(f140,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f112,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f183,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f54,f114,f63])).

fof(f360,plain,(
    k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,sK0))) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f54,f347,f63])).

fof(f347,plain,(
    r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f55,f281])).

fof(f281,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f82,f185])).

fof(f185,plain,(
    ! [X0] : k2_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f114,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f139,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f112,f60])).

fof(f169,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f168,f117])).

fof(f168,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) ),
    inference(unit_resulting_resolution,[],[f56,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f96])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f56,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:25:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (24203)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (24195)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (24196)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (24212)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (24197)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (24194)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.37/0.54  % (24211)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.37/0.54  % (24206)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.37/0.55  % (24193)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.37/0.55  % (24220)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.37/0.55  % (24218)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.37/0.55  % (24221)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.37/0.55  % (24208)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.37/0.55  % (24204)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.37/0.55  % (24209)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.37/0.55  % (24210)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.37/0.56  % (24213)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.37/0.56  % (24201)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.37/0.56  % (24200)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.37/0.56  % (24202)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.57/0.56  % (24205)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.57/0.56  % (24199)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.57/0.56  % (24208)Refutation not found, incomplete strategy% (24208)------------------------------
% 1.57/0.56  % (24208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (24208)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (24208)Memory used [KB]: 10618
% 1.57/0.56  % (24208)Time elapsed: 0.156 s
% 1.57/0.56  % (24208)------------------------------
% 1.57/0.56  % (24208)------------------------------
% 1.57/0.57  % (24216)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.57/0.58  % (24202)Refutation not found, incomplete strategy% (24202)------------------------------
% 1.57/0.58  % (24202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (24202)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (24202)Memory used [KB]: 10746
% 1.57/0.58  % (24202)Time elapsed: 0.166 s
% 1.57/0.58  % (24202)------------------------------
% 1.57/0.58  % (24202)------------------------------
% 1.57/0.58  % (24220)Refutation not found, incomplete strategy% (24220)------------------------------
% 1.57/0.58  % (24220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (24220)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (24220)Memory used [KB]: 10746
% 1.57/0.58  % (24220)Time elapsed: 0.165 s
% 1.57/0.58  % (24220)------------------------------
% 1.57/0.58  % (24220)------------------------------
% 1.57/0.58  % (24219)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.57/0.58  % (24192)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.57/0.58  % (24215)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.57/0.59  % (24214)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.57/0.59  % (24207)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.57/0.60  % (24217)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.57/0.60  % (24198)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.15/0.64  % (24195)Refutation not found, incomplete strategy% (24195)------------------------------
% 2.15/0.64  % (24195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.64  % (24195)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.64  
% 2.15/0.64  % (24195)Memory used [KB]: 6140
% 2.15/0.64  % (24195)Time elapsed: 0.220 s
% 2.15/0.64  % (24195)------------------------------
% 2.15/0.64  % (24195)------------------------------
% 2.41/0.70  % (24244)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.41/0.71  % (24243)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.78/0.75  % (24245)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.87/0.75  % (24245)Refutation not found, incomplete strategy% (24245)------------------------------
% 2.87/0.75  % (24245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.87/0.75  % (24245)Termination reason: Refutation not found, incomplete strategy
% 2.87/0.75  
% 2.87/0.75  % (24245)Memory used [KB]: 6140
% 2.87/0.75  % (24245)Time elapsed: 0.149 s
% 2.87/0.75  % (24245)------------------------------
% 2.87/0.75  % (24245)------------------------------
% 2.87/0.76  % (24203)Refutation found. Thanks to Tanya!
% 2.87/0.76  % SZS status Theorem for theBenchmark
% 2.87/0.77  % SZS output start Proof for theBenchmark
% 2.87/0.77  fof(f3033,plain,(
% 2.87/0.77    $false),
% 2.87/0.77    inference(subsumption_resolution,[],[f3032,f137])).
% 2.87/0.77  fof(f137,plain,(
% 2.87/0.77    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 2.87/0.77    inference(backward_demodulation,[],[f132,f131])).
% 2.87/0.77  fof(f131,plain,(
% 2.87/0.77    sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK1)))),
% 2.87/0.77    inference(unit_resulting_resolution,[],[f55,f97])).
% 2.87/0.77  fof(f97,plain,(
% 2.87/0.77    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0) )),
% 2.87/0.77    inference(definition_unfolding,[],[f72,f95])).
% 2.87/0.77  fof(f95,plain,(
% 2.87/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.87/0.77    inference(definition_unfolding,[],[f65,f94])).
% 2.87/0.77  fof(f94,plain,(
% 2.87/0.77    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.87/0.77    inference(definition_unfolding,[],[f66,f93])).
% 2.87/0.77  fof(f93,plain,(
% 2.87/0.77    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.87/0.77    inference(definition_unfolding,[],[f79,f92])).
% 2.87/0.77  fof(f92,plain,(
% 2.87/0.77    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.87/0.77    inference(definition_unfolding,[],[f86,f91])).
% 2.87/0.77  fof(f91,plain,(
% 2.87/0.77    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.87/0.77    inference(definition_unfolding,[],[f87,f90])).
% 2.87/0.77  fof(f90,plain,(
% 2.87/0.77    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.87/0.77    inference(definition_unfolding,[],[f88,f89])).
% 2.87/0.77  fof(f89,plain,(
% 2.87/0.77    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.87/0.77    inference(cnf_transformation,[],[f14])).
% 2.87/0.77  fof(f14,axiom,(
% 2.87/0.77    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.87/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.87/0.77  fof(f88,plain,(
% 2.87/0.77    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.87/0.77    inference(cnf_transformation,[],[f13])).
% 2.87/0.77  fof(f13,axiom,(
% 2.87/0.77    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.87/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.87/0.77  fof(f87,plain,(
% 2.87/0.77    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.87/0.77    inference(cnf_transformation,[],[f12])).
% 2.87/0.77  fof(f12,axiom,(
% 2.87/0.77    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.87/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.87/0.77  fof(f86,plain,(
% 2.87/0.77    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.87/0.77    inference(cnf_transformation,[],[f11])).
% 2.87/0.77  fof(f11,axiom,(
% 2.87/0.77    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.87/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.87/0.77  fof(f79,plain,(
% 2.87/0.77    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.87/0.77    inference(cnf_transformation,[],[f10])).
% 2.87/0.77  fof(f10,axiom,(
% 2.87/0.77    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.87/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.87/0.77  fof(f66,plain,(
% 2.87/0.77    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.87/0.77    inference(cnf_transformation,[],[f9])).
% 2.87/0.77  fof(f9,axiom,(
% 2.87/0.77    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.87/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.87/0.77  fof(f65,plain,(
% 2.87/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.87/0.77    inference(cnf_transformation,[],[f15])).
% 2.87/0.77  fof(f15,axiom,(
% 2.87/0.77    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.87/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.87/0.77  fof(f72,plain,(
% 2.87/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.87/0.77    inference(cnf_transformation,[],[f40])).
% 2.87/0.77  fof(f40,plain,(
% 2.87/0.77    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.87/0.77    inference(ennf_transformation,[],[f7])).
% 2.87/0.77  fof(f7,axiom,(
% 2.87/0.77    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.87/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.87/0.77  fof(f55,plain,(
% 2.87/0.77    r1_tarski(sK0,k1_relat_1(sK1))),
% 2.87/0.77    inference(cnf_transformation,[],[f48])).
% 2.87/0.78  fof(f48,plain,(
% 2.87/0.78    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 2.87/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f47])).
% 2.87/0.78  fof(f47,plain,(
% 2.87/0.78    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 2.87/0.78    introduced(choice_axiom,[])).
% 2.87/0.78  fof(f31,plain,(
% 2.87/0.78    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 2.87/0.78    inference(flattening,[],[f30])).
% 2.87/0.78  fof(f30,plain,(
% 2.87/0.78    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.87/0.78    inference(ennf_transformation,[],[f29])).
% 2.87/0.78  fof(f29,negated_conjecture,(
% 2.87/0.78    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.87/0.78    inference(negated_conjecture,[],[f28])).
% 2.87/0.78  fof(f28,conjecture,(
% 2.87/0.78    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.87/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 2.87/0.78  fof(f132,plain,(
% 2.87/0.78    k1_xboole_0 = k5_xboole_0(sK0,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK1))))),
% 2.87/0.78    inference(unit_resulting_resolution,[],[f55,f98])).
% 2.87/0.78  fof(f98,plain,(
% 2.87/0.78    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.87/0.78    inference(definition_unfolding,[],[f78,f96])).
% 2.87/0.78  fof(f96,plain,(
% 2.87/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.87/0.78    inference(definition_unfolding,[],[f67,f95])).
% 2.87/0.78  fof(f67,plain,(
% 2.87/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.87/0.78    inference(cnf_transformation,[],[f3])).
% 2.87/0.78  fof(f3,axiom,(
% 2.87/0.78    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.87/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.87/0.78  fof(f78,plain,(
% 2.87/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.87/0.78    inference(cnf_transformation,[],[f51])).
% 2.87/0.78  fof(f51,plain,(
% 2.87/0.78    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.87/0.78    inference(nnf_transformation,[],[f2])).
% 2.87/0.78  fof(f2,axiom,(
% 2.87/0.78    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.87/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.87/0.78  fof(f3032,plain,(
% 2.87/0.78    k1_xboole_0 != k5_xboole_0(sK0,sK0)),
% 2.87/0.78    inference(backward_demodulation,[],[f169,f3031])).
% 2.87/0.78  fof(f3031,plain,(
% 2.87/0.78    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 2.87/0.78    inference(forward_demodulation,[],[f3030,f2746])).
% 2.87/0.78  fof(f2746,plain,(
% 2.87/0.78    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 2.87/0.78    inference(unit_resulting_resolution,[],[f114,f2733,f76])).
% 2.87/0.78  fof(f76,plain,(
% 2.87/0.78    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.87/0.78    inference(cnf_transformation,[],[f50])).
% 2.87/0.78  fof(f50,plain,(
% 2.87/0.78    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.87/0.78    inference(flattening,[],[f49])).
% 2.87/0.78  fof(f49,plain,(
% 2.87/0.78    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.87/0.78    inference(nnf_transformation,[],[f1])).
% 2.87/0.78  fof(f1,axiom,(
% 2.87/0.78    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.87/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.87/0.78  fof(f2733,plain,(
% 2.87/0.78    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 2.87/0.78    inference(superposition,[],[f152,f2729])).
% 2.87/0.78  fof(f2729,plain,(
% 2.87/0.78    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(sK1))),
% 2.87/0.78    inference(superposition,[],[f659,f131])).
% 2.87/0.78  fof(f659,plain,(
% 2.87/0.78    ( ! [X0] : (k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1)))) )),
% 2.87/0.78    inference(superposition,[],[f117,f103])).
% 2.87/0.78  fof(f103,plain,(
% 2.87/0.78    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 2.87/0.78    inference(unit_resulting_resolution,[],[f54,f60])).
% 2.87/0.78  fof(f60,plain,(
% 2.87/0.78    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 2.87/0.78    inference(cnf_transformation,[],[f32])).
% 2.87/0.78  fof(f32,plain,(
% 2.87/0.78    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.87/0.78    inference(ennf_transformation,[],[f21])).
% 2.87/0.78  fof(f21,axiom,(
% 2.87/0.78    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 2.87/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 2.87/0.78  fof(f54,plain,(
% 2.87/0.78    v1_relat_1(sK1)),
% 2.87/0.78    inference(cnf_transformation,[],[f48])).
% 2.87/0.78  fof(f117,plain,(
% 2.87/0.78    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK1,X1)))) )),
% 2.87/0.78    inference(unit_resulting_resolution,[],[f54,f100])).
% 2.87/0.78  fof(f100,plain,(
% 2.87/0.78    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 2.87/0.78    inference(definition_unfolding,[],[f80,f95])).
% 2.87/0.78  fof(f80,plain,(
% 2.87/0.78    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.87/0.78    inference(cnf_transformation,[],[f42])).
% 2.87/0.78  fof(f42,plain,(
% 2.87/0.78    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.87/0.78    inference(ennf_transformation,[],[f27])).
% 2.87/0.78  fof(f27,axiom,(
% 2.87/0.78    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.87/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 2.87/0.78  fof(f152,plain,(
% 2.87/0.78    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 2.87/0.78    inference(unit_resulting_resolution,[],[f112,f69])).
% 2.87/0.78  fof(f69,plain,(
% 2.87/0.78    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.87/0.78    inference(cnf_transformation,[],[f37])).
% 2.87/0.78  fof(f37,plain,(
% 2.87/0.78    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.87/0.78    inference(ennf_transformation,[],[f20])).
% 2.87/0.78  fof(f20,axiom,(
% 2.87/0.78    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.87/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 2.87/0.78  fof(f112,plain,(
% 2.87/0.78    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 2.87/0.78    inference(unit_resulting_resolution,[],[f54,f68])).
% 2.87/0.78  fof(f68,plain,(
% 2.87/0.78    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.87/0.78    inference(cnf_transformation,[],[f36])).
% 2.87/0.78  fof(f36,plain,(
% 2.87/0.78    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.87/0.78    inference(ennf_transformation,[],[f17])).
% 2.87/0.78  fof(f17,axiom,(
% 2.87/0.78    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.87/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.87/0.78  fof(f114,plain,(
% 2.87/0.78    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) )),
% 2.87/0.78    inference(unit_resulting_resolution,[],[f54,f70])).
% 2.87/0.78  fof(f70,plain,(
% 2.87/0.78    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 2.87/0.78    inference(cnf_transformation,[],[f38])).
% 2.87/0.78  fof(f38,plain,(
% 2.87/0.78    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.87/0.78    inference(ennf_transformation,[],[f25])).
% 2.87/0.78  fof(f25,axiom,(
% 2.87/0.78    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.87/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 2.87/0.78  fof(f3030,plain,(
% 2.87/0.78    k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k1_relat_1(k7_relat_1(sK1,sK0))),
% 2.87/0.78    inference(superposition,[],[f139,f2835])).
% 2.87/0.78  fof(f2835,plain,(
% 2.87/0.78    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 2.87/0.78    inference(forward_demodulation,[],[f2773,f129])).
% 2.87/0.78  fof(f129,plain,(
% 2.87/0.78    k9_relat_1(sK1,sK0) = k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0)),
% 2.87/0.78    inference(unit_resulting_resolution,[],[f54,f55,f63])).
% 2.87/0.78  fof(f63,plain,(
% 2.87/0.78    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 2.87/0.78    inference(cnf_transformation,[],[f35])).
% 2.87/0.78  fof(f35,plain,(
% 2.87/0.78    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 2.87/0.78    inference(ennf_transformation,[],[f19])).
% 2.87/0.78  fof(f19,axiom,(
% 2.87/0.78    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 2.87/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 2.87/0.78  fof(f2773,plain,(
% 2.87/0.78    k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 2.87/0.78    inference(backward_demodulation,[],[f373,f2746])).
% 2.87/0.78  fof(f373,plain,(
% 2.87/0.78    k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,sK0))) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 2.87/0.78    inference(forward_demodulation,[],[f360,f193])).
% 2.87/0.78  fof(f193,plain,(
% 2.87/0.78    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 2.87/0.78    inference(forward_demodulation,[],[f183,f140])).
% 2.87/0.78  fof(f140,plain,(
% 2.87/0.78    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 2.87/0.78    inference(unit_resulting_resolution,[],[f112,f61])).
% 2.87/0.78  fof(f61,plain,(
% 2.87/0.78    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 2.87/0.78    inference(cnf_transformation,[],[f33])).
% 2.87/0.78  fof(f33,plain,(
% 2.87/0.78    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.87/0.78    inference(ennf_transformation,[],[f18])).
% 2.87/0.78  fof(f18,axiom,(
% 2.87/0.78    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.87/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 2.87/0.78  fof(f183,plain,(
% 2.87/0.78    ( ! [X0] : (k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 2.87/0.78    inference(unit_resulting_resolution,[],[f54,f114,f63])).
% 2.87/0.78  fof(f360,plain,(
% 2.87/0.78    k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,sK0))) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 2.87/0.78    inference(unit_resulting_resolution,[],[f54,f347,f63])).
% 2.87/0.78  fof(f347,plain,(
% 2.87/0.78    r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))),
% 2.87/0.78    inference(unit_resulting_resolution,[],[f55,f281])).
% 2.87/0.78  fof(f281,plain,(
% 2.87/0.78    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X1) | ~r1_tarski(X0,X1)) )),
% 2.87/0.78    inference(superposition,[],[f82,f185])).
% 2.87/0.78  fof(f185,plain,(
% 2.87/0.78    ( ! [X0] : (k2_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0) = X0) )),
% 2.87/0.78    inference(unit_resulting_resolution,[],[f114,f73])).
% 2.87/0.78  fof(f73,plain,(
% 2.87/0.78    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.87/0.78    inference(cnf_transformation,[],[f41])).
% 2.87/0.78  fof(f41,plain,(
% 2.87/0.78    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.87/0.78    inference(ennf_transformation,[],[f5])).
% 2.87/0.78  fof(f5,axiom,(
% 2.87/0.78    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.87/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.87/0.78  fof(f82,plain,(
% 2.87/0.78    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.87/0.78    inference(cnf_transformation,[],[f44])).
% 2.87/0.78  fof(f44,plain,(
% 2.87/0.78    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.87/0.78    inference(ennf_transformation,[],[f4])).
% 2.87/0.78  fof(f4,axiom,(
% 2.87/0.78    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.87/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.87/0.78  fof(f139,plain,(
% 2.87/0.78    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) )),
% 2.87/0.78    inference(unit_resulting_resolution,[],[f112,f60])).
% 2.87/0.78  fof(f169,plain,(
% 2.87/0.78    k1_xboole_0 != k5_xboole_0(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)))),
% 2.87/0.78    inference(forward_demodulation,[],[f168,f117])).
% 2.87/0.78  fof(f168,plain,(
% 2.87/0.78    k1_xboole_0 != k5_xboole_0(sK0,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))))),
% 2.87/0.78    inference(unit_resulting_resolution,[],[f56,f99])).
% 2.87/0.78  fof(f99,plain,(
% 2.87/0.78    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r1_tarski(X0,X1)) )),
% 2.87/0.78    inference(definition_unfolding,[],[f77,f96])).
% 2.87/0.78  fof(f77,plain,(
% 2.87/0.78    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.87/0.78    inference(cnf_transformation,[],[f51])).
% 2.87/0.78  fof(f56,plain,(
% 2.87/0.78    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 2.87/0.78    inference(cnf_transformation,[],[f48])).
% 2.87/0.78  % SZS output end Proof for theBenchmark
% 2.87/0.78  % (24203)------------------------------
% 2.87/0.78  % (24203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.87/0.78  % (24203)Termination reason: Refutation
% 2.87/0.78  
% 2.87/0.78  % (24203)Memory used [KB]: 9850
% 2.87/0.78  % (24203)Time elapsed: 0.336 s
% 2.87/0.78  % (24203)------------------------------
% 2.87/0.78  % (24203)------------------------------
% 2.87/0.78  % (24191)Success in time 0.414 s
%------------------------------------------------------------------------------
