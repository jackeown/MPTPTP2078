%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:51 EST 2020

% Result     : Theorem 4.08s
% Output     : Refutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 562 expanded)
%              Number of leaves         :   22 ( 157 expanded)
%              Depth                    :   20
%              Number of atoms          :  233 (1133 expanded)
%              Number of equality atoms :   93 ( 318 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5094,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5079,f48])).

fof(f48,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f42])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f5079,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f1272,f5066])).

fof(f5066,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f5031,f2763])).

fof(f2763,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f2742,f508])).

fof(f508,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(k7_relat_1(sK1,X1)))
      | k1_relat_1(k7_relat_1(sK1,X1)) = X1 ) ),
    inference(forward_demodulation,[],[f507,f50])).

fof(f50,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f507,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(k7_relat_1(sK1,X1)))
      | k1_relat_1(k6_relat_1(X1)) = k1_relat_1(k7_relat_1(sK1,X1)) ) ),
    inference(forward_demodulation,[],[f506,f50])).

fof(f506,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k7_relat_1(sK1,X1)))
      | k1_relat_1(k6_relat_1(X1)) = k1_relat_1(k7_relat_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f503,f49])).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f503,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k7_relat_1(sK1,X1)))
      | k1_relat_1(k6_relat_1(X1)) = k1_relat_1(k7_relat_1(sK1,X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f103,f187])).

fof(f187,plain,(
    ! [X2] : k1_relat_1(k7_relat_1(sK1,X2)) = k10_relat_1(k6_relat_1(X2),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f184,f134])).

fof(f134,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    inference(resolution,[],[f60,f46])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f184,plain,(
    ! [X2] : k1_relat_1(k5_relat_1(k6_relat_1(X2),sK1)) = k10_relat_1(k6_relat_1(X2),k1_relat_1(sK1)) ),
    inference(resolution,[],[f181,f49])).

fof(f181,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k1_relat_1(k5_relat_1(X7,sK1)) = k10_relat_1(X7,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f54,f46])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f103,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(k1_relat_1(X5),k10_relat_1(X5,X6))
      | k1_relat_1(X5) = k10_relat_1(X5,X6)
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f67,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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

fof(f2742,plain,(
    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f2741,f187])).

fof(f2741,plain,(
    r1_tarski(sK0,k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f2740,f422])).

fof(f422,plain,(
    ! [X4,X5] : k10_relat_1(k6_relat_1(X4),X5) = k1_relat_1(k7_relat_1(k6_relat_1(X5),X4)) ),
    inference(forward_demodulation,[],[f418,f135])).

fof(f135,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f60,f49])).

fof(f418,plain,(
    ! [X4,X5] : k10_relat_1(k6_relat_1(X4),X5) = k1_relat_1(k5_relat_1(k6_relat_1(X4),k6_relat_1(X5))) ),
    inference(resolution,[],[f182,f49])).

fof(f182,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k1_relat_1(k5_relat_1(X3,k6_relat_1(X4))) = k10_relat_1(X3,X4) ) ),
    inference(forward_demodulation,[],[f179,f50])).

fof(f179,plain,(
    ! [X4,X3] :
      ( k1_relat_1(k5_relat_1(X3,k6_relat_1(X4))) = k10_relat_1(X3,k1_relat_1(k6_relat_1(X4)))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f54,f49])).

fof(f2740,plain,(
    r1_tarski(sK0,k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0))) ),
    inference(subsumption_resolution,[],[f2729,f328])).

fof(f328,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(subsumption_resolution,[],[f327,f49])).

fof(f327,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f326,f49])).

fof(f326,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f64,f135])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f2729,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)))
    | ~ v1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)) ),
    inference(superposition,[],[f58,f2682])).

fof(f2682,plain,(
    sK0 = k10_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0),sK0) ),
    inference(superposition,[],[f758,f1213])).

fof(f1213,plain,(
    sK0 = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) ),
    inference(forward_demodulation,[],[f1200,f50])).

fof(f1200,plain,(
    k1_relat_1(k6_relat_1(sK0)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) ),
    inference(superposition,[],[f422,f358])).

fof(f358,plain,(
    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f165,f47])).

fof(f47,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f164,f49])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f61,f50])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f758,plain,(
    ! [X4,X3] : k10_relat_1(k6_relat_1(X3),X4) = k10_relat_1(k7_relat_1(k6_relat_1(X3),k10_relat_1(k6_relat_1(X3),X4)),X4) ),
    inference(superposition,[],[f266,f77])).

fof(f77,plain,(
    ! [X0] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f266,plain,(
    ! [X6,X8,X7] : k10_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8) = k1_setfam_1(k4_enumset1(X7,X7,X7,X7,X7,k10_relat_1(k6_relat_1(X6),X8))) ),
    inference(resolution,[],[f78,f49])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f69,f76])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f5031,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f142,f5027])).

fof(f5027,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f5025,f971])).

fof(f971,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0) ),
    inference(superposition,[],[f291,f93])).

fof(f93,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f92,f51])).

fof(f51,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f92,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f90,f50])).

fof(f90,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f53,f49])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f291,plain,(
    ! [X4,X5] : k9_relat_1(sK1,k9_relat_1(k6_relat_1(X4),X5)) = k9_relat_1(k7_relat_1(sK1,X4),X5) ),
    inference(forward_demodulation,[],[f288,f134])).

fof(f288,plain,(
    ! [X4,X5] : k9_relat_1(k5_relat_1(k6_relat_1(X4),sK1),X5) = k9_relat_1(sK1,k9_relat_1(k6_relat_1(X4),X5)) ),
    inference(resolution,[],[f214,f49])).

fof(f214,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | k9_relat_1(k5_relat_1(X10,sK1),X11) = k9_relat_1(sK1,k9_relat_1(X10,X11)) ) ),
    inference(resolution,[],[f62,f46])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f5025,plain,(
    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0) ),
    inference(superposition,[],[f141,f2763])).

fof(f141,plain,(
    ! [X2] : k9_relat_1(k7_relat_1(sK1,X2),k1_relat_1(k7_relat_1(sK1,X2))) = k2_relat_1(k7_relat_1(sK1,X2)) ),
    inference(resolution,[],[f139,f53])).

fof(f139,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(subsumption_resolution,[],[f138,f49])).

fof(f138,plain,(
    ! [X0] :
      ( v1_relat_1(k7_relat_1(sK1,X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f137,f46])).

fof(f137,plain,(
    ! [X0] :
      ( v1_relat_1(k7_relat_1(sK1,X0))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f64,f134])).

fof(f142,plain,(
    ! [X3] : k1_relat_1(k7_relat_1(sK1,X3)) = k10_relat_1(k7_relat_1(sK1,X3),k2_relat_1(k7_relat_1(sK1,X3))) ),
    inference(resolution,[],[f139,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f1272,plain,(
    ! [X2,X3] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X2),X3),k10_relat_1(sK1,X3)) ),
    inference(superposition,[],[f1194,f314])).

fof(f314,plain,(
    ! [X4,X5] : k10_relat_1(k6_relat_1(X4),k10_relat_1(sK1,X5)) = k10_relat_1(k7_relat_1(sK1,X4),X5) ),
    inference(forward_demodulation,[],[f311,f134])).

fof(f311,plain,(
    ! [X4,X5] : k10_relat_1(k5_relat_1(k6_relat_1(X4),sK1),X5) = k10_relat_1(k6_relat_1(X4),k10_relat_1(sK1,X5)) ),
    inference(resolution,[],[f247,f49])).

fof(f247,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | k10_relat_1(k5_relat_1(X12,sK1),X13) = k10_relat_1(X12,k10_relat_1(sK1,X13)) ) ),
    inference(resolution,[],[f63,f46])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f1194,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X1),X0),X0) ),
    inference(backward_demodulation,[],[f99,f422])).

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    inference(subsumption_resolution,[],[f98,f49])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f59,f50])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:44:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (21671)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (21672)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (21675)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (21688)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.53  % (21680)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (21669)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (21686)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (21663)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (21664)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (21678)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (21665)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (21666)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (21692)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (21670)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (21667)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (21682)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (21673)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (21687)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (21689)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (21683)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (21691)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (21676)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (21679)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (21668)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.56  % (21681)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (21674)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (21684)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (21690)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.58  % (21677)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.58  % (21685)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.25/0.70  % (21666)Refutation not found, incomplete strategy% (21666)------------------------------
% 2.25/0.70  % (21666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.68/0.71  % (21666)Termination reason: Refutation not found, incomplete strategy
% 2.68/0.71  
% 2.68/0.71  % (21666)Memory used [KB]: 6268
% 2.68/0.71  % (21666)Time elapsed: 0.288 s
% 2.68/0.71  % (21666)------------------------------
% 2.68/0.71  % (21666)------------------------------
% 3.03/0.80  % (21687)Time limit reached!
% 3.03/0.80  % (21687)------------------------------
% 3.03/0.80  % (21687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.03/0.80  % (21687)Termination reason: Time limit
% 3.03/0.80  % (21687)Termination phase: Saturation
% 3.03/0.80  
% 3.03/0.80  % (21687)Memory used [KB]: 12665
% 3.03/0.80  % (21687)Time elapsed: 0.400 s
% 3.03/0.80  % (21687)------------------------------
% 3.03/0.80  % (21687)------------------------------
% 3.74/0.85  % (21665)Time limit reached!
% 3.74/0.85  % (21665)------------------------------
% 3.74/0.85  % (21665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/0.85  % (21665)Termination reason: Time limit
% 3.74/0.85  
% 3.74/0.85  % (21665)Memory used [KB]: 7803
% 3.74/0.85  % (21665)Time elapsed: 0.435 s
% 3.74/0.85  % (21665)------------------------------
% 3.74/0.85  % (21665)------------------------------
% 3.74/0.85  % (21726)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 4.08/0.90  % (21669)Refutation found. Thanks to Tanya!
% 4.08/0.90  % SZS status Theorem for theBenchmark
% 4.08/0.90  % SZS output start Proof for theBenchmark
% 4.08/0.92  fof(f5094,plain,(
% 4.08/0.92    $false),
% 4.08/0.92    inference(subsumption_resolution,[],[f5079,f48])).
% 4.08/0.92  fof(f48,plain,(
% 4.08/0.92    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 4.08/0.92    inference(cnf_transformation,[],[f43])).
% 4.08/0.92  fof(f43,plain,(
% 4.08/0.92    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 4.08/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f42])).
% 4.08/0.92  fof(f42,plain,(
% 4.08/0.92    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 4.08/0.92    introduced(choice_axiom,[])).
% 4.08/0.92  fof(f26,plain,(
% 4.08/0.92    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 4.08/0.92    inference(flattening,[],[f25])).
% 4.08/0.92  fof(f25,plain,(
% 4.08/0.92    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 4.08/0.92    inference(ennf_transformation,[],[f23])).
% 4.08/0.92  fof(f23,negated_conjecture,(
% 4.08/0.92    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 4.08/0.92    inference(negated_conjecture,[],[f22])).
% 4.08/0.92  fof(f22,conjecture,(
% 4.08/0.92    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 4.08/0.92  fof(f5079,plain,(
% 4.08/0.92    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 4.08/0.92    inference(superposition,[],[f1272,f5066])).
% 4.08/0.92  fof(f5066,plain,(
% 4.08/0.92    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 4.08/0.92    inference(forward_demodulation,[],[f5031,f2763])).
% 4.08/0.92  fof(f2763,plain,(
% 4.08/0.92    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 4.08/0.92    inference(resolution,[],[f2742,f508])).
% 4.08/0.92  fof(f508,plain,(
% 4.08/0.92    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(k7_relat_1(sK1,X1))) | k1_relat_1(k7_relat_1(sK1,X1)) = X1) )),
% 4.08/0.92    inference(forward_demodulation,[],[f507,f50])).
% 4.08/0.92  fof(f50,plain,(
% 4.08/0.92    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 4.08/0.92    inference(cnf_transformation,[],[f17])).
% 4.08/0.92  fof(f17,axiom,(
% 4.08/0.92    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 4.08/0.92  fof(f507,plain,(
% 4.08/0.92    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(k7_relat_1(sK1,X1))) | k1_relat_1(k6_relat_1(X1)) = k1_relat_1(k7_relat_1(sK1,X1))) )),
% 4.08/0.92    inference(forward_demodulation,[],[f506,f50])).
% 4.08/0.92  fof(f506,plain,(
% 4.08/0.92    ( ! [X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k7_relat_1(sK1,X1))) | k1_relat_1(k6_relat_1(X1)) = k1_relat_1(k7_relat_1(sK1,X1))) )),
% 4.08/0.92    inference(subsumption_resolution,[],[f503,f49])).
% 4.08/0.92  fof(f49,plain,(
% 4.08/0.92    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 4.08/0.92    inference(cnf_transformation,[],[f10])).
% 4.08/0.92  fof(f10,axiom,(
% 4.08/0.92    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 4.08/0.92  fof(f503,plain,(
% 4.08/0.92    ( ! [X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k7_relat_1(sK1,X1))) | k1_relat_1(k6_relat_1(X1)) = k1_relat_1(k7_relat_1(sK1,X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 4.08/0.92    inference(superposition,[],[f103,f187])).
% 4.08/0.92  fof(f187,plain,(
% 4.08/0.92    ( ! [X2] : (k1_relat_1(k7_relat_1(sK1,X2)) = k10_relat_1(k6_relat_1(X2),k1_relat_1(sK1))) )),
% 4.08/0.92    inference(forward_demodulation,[],[f184,f134])).
% 4.08/0.92  fof(f134,plain,(
% 4.08/0.92    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) )),
% 4.08/0.92    inference(resolution,[],[f60,f46])).
% 4.08/0.92  fof(f46,plain,(
% 4.08/0.92    v1_relat_1(sK1)),
% 4.08/0.92    inference(cnf_transformation,[],[f43])).
% 4.08/0.92  fof(f60,plain,(
% 4.08/0.92    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f32])).
% 4.08/0.92  fof(f32,plain,(
% 4.08/0.92    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 4.08/0.92    inference(ennf_transformation,[],[f19])).
% 4.08/0.92  fof(f19,axiom,(
% 4.08/0.92    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 4.08/0.92  fof(f184,plain,(
% 4.08/0.92    ( ! [X2] : (k1_relat_1(k5_relat_1(k6_relat_1(X2),sK1)) = k10_relat_1(k6_relat_1(X2),k1_relat_1(sK1))) )),
% 4.08/0.92    inference(resolution,[],[f181,f49])).
% 4.08/0.92  fof(f181,plain,(
% 4.08/0.92    ( ! [X7] : (~v1_relat_1(X7) | k1_relat_1(k5_relat_1(X7,sK1)) = k10_relat_1(X7,k1_relat_1(sK1))) )),
% 4.08/0.92    inference(resolution,[],[f54,f46])).
% 4.08/0.92  fof(f54,plain,(
% 4.08/0.92    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f29])).
% 4.08/0.92  fof(f29,plain,(
% 4.08/0.92    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.08/0.92    inference(ennf_transformation,[],[f16])).
% 4.08/0.92  fof(f16,axiom,(
% 4.08/0.92    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 4.08/0.92  fof(f103,plain,(
% 4.08/0.92    ( ! [X6,X5] : (~r1_tarski(k1_relat_1(X5),k10_relat_1(X5,X6)) | k1_relat_1(X5) = k10_relat_1(X5,X6) | ~v1_relat_1(X5)) )),
% 4.08/0.92    inference(resolution,[],[f67,f58])).
% 4.08/0.92  fof(f58,plain,(
% 4.08/0.92    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f30])).
% 4.08/0.92  fof(f30,plain,(
% 4.08/0.92    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 4.08/0.92    inference(ennf_transformation,[],[f13])).
% 4.08/0.92  fof(f13,axiom,(
% 4.08/0.92    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 4.08/0.92  fof(f67,plain,(
% 4.08/0.92    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f45])).
% 4.08/0.92  fof(f45,plain,(
% 4.08/0.92    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.08/0.92    inference(flattening,[],[f44])).
% 4.08/0.92  fof(f44,plain,(
% 4.08/0.92    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.08/0.92    inference(nnf_transformation,[],[f2])).
% 4.08/0.92  fof(f2,axiom,(
% 4.08/0.92    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.08/0.92  fof(f2742,plain,(
% 4.08/0.92    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 4.08/0.92    inference(forward_demodulation,[],[f2741,f187])).
% 4.08/0.92  fof(f2741,plain,(
% 4.08/0.92    r1_tarski(sK0,k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)))),
% 4.08/0.92    inference(forward_demodulation,[],[f2740,f422])).
% 4.08/0.92  fof(f422,plain,(
% 4.08/0.92    ( ! [X4,X5] : (k10_relat_1(k6_relat_1(X4),X5) = k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) )),
% 4.08/0.92    inference(forward_demodulation,[],[f418,f135])).
% 4.08/0.92  fof(f135,plain,(
% 4.08/0.92    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 4.08/0.92    inference(resolution,[],[f60,f49])).
% 4.08/0.92  fof(f418,plain,(
% 4.08/0.92    ( ! [X4,X5] : (k10_relat_1(k6_relat_1(X4),X5) = k1_relat_1(k5_relat_1(k6_relat_1(X4),k6_relat_1(X5)))) )),
% 4.08/0.92    inference(resolution,[],[f182,f49])).
% 4.08/0.92  fof(f182,plain,(
% 4.08/0.92    ( ! [X4,X3] : (~v1_relat_1(X3) | k1_relat_1(k5_relat_1(X3,k6_relat_1(X4))) = k10_relat_1(X3,X4)) )),
% 4.08/0.92    inference(forward_demodulation,[],[f179,f50])).
% 4.08/0.92  fof(f179,plain,(
% 4.08/0.92    ( ! [X4,X3] : (k1_relat_1(k5_relat_1(X3,k6_relat_1(X4))) = k10_relat_1(X3,k1_relat_1(k6_relat_1(X4))) | ~v1_relat_1(X3)) )),
% 4.08/0.92    inference(resolution,[],[f54,f49])).
% 4.08/0.92  fof(f2740,plain,(
% 4.08/0.92    r1_tarski(sK0,k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)))),
% 4.08/0.92    inference(subsumption_resolution,[],[f2729,f328])).
% 4.08/0.92  fof(f328,plain,(
% 4.08/0.92    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 4.08/0.92    inference(subsumption_resolution,[],[f327,f49])).
% 4.08/0.92  fof(f327,plain,(
% 4.08/0.92    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 4.08/0.92    inference(subsumption_resolution,[],[f326,f49])).
% 4.08/0.92  fof(f326,plain,(
% 4.08/0.92    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 4.08/0.92    inference(superposition,[],[f64,f135])).
% 4.08/0.92  fof(f64,plain,(
% 4.08/0.92    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f38])).
% 4.08/0.92  fof(f38,plain,(
% 4.08/0.92    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 4.08/0.92    inference(flattening,[],[f37])).
% 4.08/0.92  fof(f37,plain,(
% 4.08/0.92    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 4.08/0.92    inference(ennf_transformation,[],[f9])).
% 4.08/0.92  fof(f9,axiom,(
% 4.08/0.92    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 4.08/0.92  fof(f2729,plain,(
% 4.08/0.92    r1_tarski(sK0,k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0))) | ~v1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0))),
% 4.08/0.92    inference(superposition,[],[f58,f2682])).
% 4.08/0.92  fof(f2682,plain,(
% 4.08/0.92    sK0 = k10_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0),sK0)),
% 4.08/0.92    inference(superposition,[],[f758,f1213])).
% 4.08/0.92  fof(f1213,plain,(
% 4.08/0.92    sK0 = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)),
% 4.08/0.92    inference(forward_demodulation,[],[f1200,f50])).
% 4.08/0.92  fof(f1200,plain,(
% 4.08/0.92    k1_relat_1(k6_relat_1(sK0)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)),
% 4.08/0.92    inference(superposition,[],[f422,f358])).
% 4.08/0.92  fof(f358,plain,(
% 4.08/0.92    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),
% 4.08/0.92    inference(resolution,[],[f165,f47])).
% 4.08/0.92  fof(f47,plain,(
% 4.08/0.92    r1_tarski(sK0,k1_relat_1(sK1))),
% 4.08/0.92    inference(cnf_transformation,[],[f43])).
% 4.08/0.92  fof(f165,plain,(
% 4.08/0.92    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 4.08/0.92    inference(subsumption_resolution,[],[f164,f49])).
% 4.08/0.92  fof(f164,plain,(
% 4.08/0.92    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 4.08/0.92    inference(superposition,[],[f61,f50])).
% 4.08/0.92  fof(f61,plain,(
% 4.08/0.92    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f34])).
% 4.08/0.92  fof(f34,plain,(
% 4.08/0.92    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.08/0.92    inference(flattening,[],[f33])).
% 4.08/0.92  fof(f33,plain,(
% 4.08/0.92    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.08/0.92    inference(ennf_transformation,[],[f20])).
% 4.08/0.92  fof(f20,axiom,(
% 4.08/0.92    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 4.08/0.92  fof(f758,plain,(
% 4.08/0.92    ( ! [X4,X3] : (k10_relat_1(k6_relat_1(X3),X4) = k10_relat_1(k7_relat_1(k6_relat_1(X3),k10_relat_1(k6_relat_1(X3),X4)),X4)) )),
% 4.08/0.92    inference(superposition,[],[f266,f77])).
% 4.08/0.92  fof(f77,plain,(
% 4.08/0.92    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 4.08/0.92    inference(definition_unfolding,[],[f55,f76])).
% 4.08/0.92  fof(f76,plain,(
% 4.08/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 4.08/0.92    inference(definition_unfolding,[],[f56,f75])).
% 4.08/0.92  fof(f75,plain,(
% 4.08/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 4.08/0.92    inference(definition_unfolding,[],[f57,f74])).
% 4.08/0.92  fof(f74,plain,(
% 4.08/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 4.08/0.92    inference(definition_unfolding,[],[f68,f73])).
% 4.08/0.92  fof(f73,plain,(
% 4.08/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 4.08/0.92    inference(definition_unfolding,[],[f71,f72])).
% 4.08/0.92  fof(f72,plain,(
% 4.08/0.92    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f7])).
% 4.08/0.92  fof(f7,axiom,(
% 4.08/0.92    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 4.08/0.92  fof(f71,plain,(
% 4.08/0.92    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f6])).
% 4.08/0.92  fof(f6,axiom,(
% 4.08/0.92    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 4.08/0.92  fof(f68,plain,(
% 4.08/0.92    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f5])).
% 4.08/0.92  fof(f5,axiom,(
% 4.08/0.92    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 4.08/0.92  fof(f57,plain,(
% 4.08/0.92    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f4])).
% 4.08/0.92  fof(f4,axiom,(
% 4.08/0.92    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 4.08/0.92  fof(f56,plain,(
% 4.08/0.92    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f8])).
% 4.08/0.92  fof(f8,axiom,(
% 4.08/0.92    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 4.08/0.92  fof(f55,plain,(
% 4.08/0.92    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.08/0.92    inference(cnf_transformation,[],[f24])).
% 4.08/0.92  fof(f24,plain,(
% 4.08/0.92    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 4.08/0.92    inference(rectify,[],[f1])).
% 4.08/0.92  fof(f1,axiom,(
% 4.08/0.92    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 4.08/0.92  fof(f266,plain,(
% 4.08/0.92    ( ! [X6,X8,X7] : (k10_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8) = k1_setfam_1(k4_enumset1(X7,X7,X7,X7,X7,k10_relat_1(k6_relat_1(X6),X8)))) )),
% 4.08/0.92    inference(resolution,[],[f78,f49])).
% 4.08/0.92  fof(f78,plain,(
% 4.08/0.92    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 4.08/0.92    inference(definition_unfolding,[],[f69,f76])).
% 4.08/0.92  fof(f69,plain,(
% 4.08/0.92    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f39])).
% 4.08/0.92  fof(f39,plain,(
% 4.08/0.92    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 4.08/0.92    inference(ennf_transformation,[],[f21])).
% 4.08/0.92  fof(f21,axiom,(
% 4.08/0.92    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 4.08/0.92  fof(f5031,plain,(
% 4.08/0.92    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 4.08/0.92    inference(superposition,[],[f142,f5027])).
% 4.08/0.92  fof(f5027,plain,(
% 4.08/0.92    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 4.08/0.92    inference(forward_demodulation,[],[f5025,f971])).
% 4.08/0.92  fof(f971,plain,(
% 4.08/0.92    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0)) )),
% 4.08/0.92    inference(superposition,[],[f291,f93])).
% 4.08/0.92  fof(f93,plain,(
% 4.08/0.92    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 4.08/0.92    inference(forward_demodulation,[],[f92,f51])).
% 4.08/0.92  fof(f51,plain,(
% 4.08/0.92    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 4.08/0.92    inference(cnf_transformation,[],[f17])).
% 4.08/0.92  fof(f92,plain,(
% 4.08/0.92    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) )),
% 4.08/0.92    inference(forward_demodulation,[],[f90,f50])).
% 4.08/0.92  fof(f90,plain,(
% 4.08/0.92    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 4.08/0.92    inference(resolution,[],[f53,f49])).
% 4.08/0.92  fof(f53,plain,(
% 4.08/0.92    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f28])).
% 4.08/0.92  fof(f28,plain,(
% 4.08/0.92    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 4.08/0.92    inference(ennf_transformation,[],[f11])).
% 4.08/0.92  fof(f11,axiom,(
% 4.08/0.92    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 4.08/0.92  fof(f291,plain,(
% 4.08/0.92    ( ! [X4,X5] : (k9_relat_1(sK1,k9_relat_1(k6_relat_1(X4),X5)) = k9_relat_1(k7_relat_1(sK1,X4),X5)) )),
% 4.08/0.92    inference(forward_demodulation,[],[f288,f134])).
% 4.08/0.92  fof(f288,plain,(
% 4.08/0.92    ( ! [X4,X5] : (k9_relat_1(k5_relat_1(k6_relat_1(X4),sK1),X5) = k9_relat_1(sK1,k9_relat_1(k6_relat_1(X4),X5))) )),
% 4.08/0.92    inference(resolution,[],[f214,f49])).
% 4.08/0.92  fof(f214,plain,(
% 4.08/0.92    ( ! [X10,X11] : (~v1_relat_1(X10) | k9_relat_1(k5_relat_1(X10,sK1),X11) = k9_relat_1(sK1,k9_relat_1(X10,X11))) )),
% 4.08/0.92    inference(resolution,[],[f62,f46])).
% 4.08/0.92  fof(f62,plain,(
% 4.08/0.92    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f35])).
% 4.08/0.92  fof(f35,plain,(
% 4.08/0.92    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.08/0.92    inference(ennf_transformation,[],[f12])).
% 4.08/0.92  fof(f12,axiom,(
% 4.08/0.92    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 4.08/0.92  fof(f5025,plain,(
% 4.08/0.92    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0)),
% 4.08/0.92    inference(superposition,[],[f141,f2763])).
% 4.08/0.92  fof(f141,plain,(
% 4.08/0.92    ( ! [X2] : (k9_relat_1(k7_relat_1(sK1,X2),k1_relat_1(k7_relat_1(sK1,X2))) = k2_relat_1(k7_relat_1(sK1,X2))) )),
% 4.08/0.92    inference(resolution,[],[f139,f53])).
% 4.08/0.92  fof(f139,plain,(
% 4.08/0.92    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 4.08/0.92    inference(subsumption_resolution,[],[f138,f49])).
% 4.08/0.92  fof(f138,plain,(
% 4.08/0.92    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 4.08/0.92    inference(subsumption_resolution,[],[f137,f46])).
% 4.08/0.92  fof(f137,plain,(
% 4.08/0.92    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0)) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 4.08/0.92    inference(superposition,[],[f64,f134])).
% 4.08/0.92  fof(f142,plain,(
% 4.08/0.92    ( ! [X3] : (k1_relat_1(k7_relat_1(sK1,X3)) = k10_relat_1(k7_relat_1(sK1,X3),k2_relat_1(k7_relat_1(sK1,X3)))) )),
% 4.08/0.92    inference(resolution,[],[f139,f52])).
% 4.08/0.92  fof(f52,plain,(
% 4.08/0.92    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 4.08/0.92    inference(cnf_transformation,[],[f27])).
% 4.08/0.92  fof(f27,plain,(
% 4.08/0.92    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.08/0.92    inference(ennf_transformation,[],[f14])).
% 4.08/0.92  fof(f14,axiom,(
% 4.08/0.92    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 4.08/0.92  fof(f1272,plain,(
% 4.08/0.92    ( ! [X2,X3] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X2),X3),k10_relat_1(sK1,X3))) )),
% 4.08/0.92    inference(superposition,[],[f1194,f314])).
% 4.08/0.92  fof(f314,plain,(
% 4.08/0.92    ( ! [X4,X5] : (k10_relat_1(k6_relat_1(X4),k10_relat_1(sK1,X5)) = k10_relat_1(k7_relat_1(sK1,X4),X5)) )),
% 4.08/0.92    inference(forward_demodulation,[],[f311,f134])).
% 4.08/0.92  fof(f311,plain,(
% 4.08/0.92    ( ! [X4,X5] : (k10_relat_1(k5_relat_1(k6_relat_1(X4),sK1),X5) = k10_relat_1(k6_relat_1(X4),k10_relat_1(sK1,X5))) )),
% 4.08/0.92    inference(resolution,[],[f247,f49])).
% 4.08/0.92  fof(f247,plain,(
% 4.08/0.92    ( ! [X12,X13] : (~v1_relat_1(X12) | k10_relat_1(k5_relat_1(X12,sK1),X13) = k10_relat_1(X12,k10_relat_1(sK1,X13))) )),
% 4.08/0.92    inference(resolution,[],[f63,f46])).
% 4.08/0.92  fof(f63,plain,(
% 4.08/0.92    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X1)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f36])).
% 4.08/0.92  fof(f36,plain,(
% 4.08/0.92    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.08/0.92    inference(ennf_transformation,[],[f15])).
% 4.08/0.92  fof(f15,axiom,(
% 4.08/0.92    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 4.08/0.92  fof(f1194,plain,(
% 4.08/0.92    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X1),X0),X0)) )),
% 4.08/0.92    inference(backward_demodulation,[],[f99,f422])).
% 4.08/0.92  fof(f99,plain,(
% 4.08/0.92    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) )),
% 4.08/0.92    inference(subsumption_resolution,[],[f98,f49])).
% 4.08/0.92  fof(f98,plain,(
% 4.08/0.92    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 4.08/0.92    inference(superposition,[],[f59,f50])).
% 4.08/0.92  fof(f59,plain,(
% 4.08/0.92    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.08/0.92    inference(cnf_transformation,[],[f31])).
% 4.08/0.92  fof(f31,plain,(
% 4.08/0.92    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 4.08/0.92    inference(ennf_transformation,[],[f18])).
% 4.08/0.92  fof(f18,axiom,(
% 4.08/0.92    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 4.08/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 4.08/0.92  % SZS output end Proof for theBenchmark
% 4.08/0.92  % (21669)------------------------------
% 4.08/0.92  % (21669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/0.92  % (21669)Termination reason: Refutation
% 4.08/0.92  
% 4.08/0.92  % (21669)Memory used [KB]: 15607
% 4.08/0.92  % (21669)Time elapsed: 0.494 s
% 4.08/0.92  % (21669)------------------------------
% 4.08/0.92  % (21669)------------------------------
% 4.08/0.92  % (21662)Success in time 0.561 s
%------------------------------------------------------------------------------
