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
% DateTime   : Thu Dec  3 12:53:51 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 375 expanded)
%              Number of leaves         :   28 ( 101 expanded)
%              Depth                    :   22
%              Number of atoms          :  237 ( 812 expanded)
%              Number of equality atoms :   98 ( 251 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1179,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1178,f53])).

fof(f53,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f46])).

fof(f46,plain,
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

fof(f1178,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1176,f154])).

fof(f154,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f153,f96])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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

fof(f153,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f93,f92])).

fof(f92,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f61,f90])).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f63,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f76,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f81,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f82,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f83,f84])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f64,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f61,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f75,f91])).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f65,f90])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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

fof(f1176,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f206,f1138])).

fof(f1138,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f1137,f1065])).

fof(f1065,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f1061,f51])).

fof(f51,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f1061,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f1026,f118])).

fof(f118,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,k1_relat_1(k7_relat_1(X7,X6)))
      | k1_relat_1(k7_relat_1(X7,X6)) = X6
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f73,f68])).

fof(f68,plain,(
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

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1026,plain,(
    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1018,f51])).

fof(f1018,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f1010,f69])).

fof(f69,plain,(
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

fof(f1010,plain,(
    r1_tarski(sK0,k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(superposition,[],[f936,f106])).

fof(f106,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f105,f55])).

fof(f55,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f105,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f103,f56])).

fof(f56,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f103,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f57,f54])).

fof(f54,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f57,plain,(
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

fof(f936,plain,(
    ! [X17] : r1_tarski(k10_relat_1(k6_relat_1(X17),sK0),k1_relat_1(k5_relat_1(k6_relat_1(X17),sK1))) ),
    inference(forward_demodulation,[],[f931,f135])).

fof(f135,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f130,f54])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f59,f51])).

fof(f59,plain,(
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

fof(f931,plain,(
    ! [X17] : r1_tarski(k10_relat_1(k6_relat_1(X17),sK0),k10_relat_1(k6_relat_1(X17),k1_relat_1(sK1))) ),
    inference(superposition,[],[f259,f896])).

fof(f896,plain,(
    k1_relat_1(sK1) = k2_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f891,f96])).

fof(f891,plain,(
    ! [X71] :
      ( ~ r1_tarski(k1_relat_1(sK1),X71)
      | k2_xboole_0(sK0,X71) = X71 ) ),
    inference(resolution,[],[f219,f52])).

fof(f52,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f219,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | k2_xboole_0(X3,X4) = X4
      | ~ r1_tarski(X5,X4) ) ),
    inference(subsumption_resolution,[],[f212,f96])).

fof(f212,plain,(
    ! [X4,X5,X3] :
      ( k2_xboole_0(X3,X4) = X4
      | ~ r1_tarski(X4,X4)
      | ~ r1_tarski(X3,X5)
      | ~ r1_tarski(X5,X4) ) ),
    inference(resolution,[],[f117,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X2,X1),X1)
      | ~ r1_tarski(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f80,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f117,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k2_xboole_0(X3,X4),X5)
      | k2_xboole_0(X3,X4) = X5
      | ~ r1_tarski(X5,X4) ) ),
    inference(resolution,[],[f73,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f259,plain,(
    ! [X2,X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k10_relat_1(k6_relat_1(X0),k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f62,f145])).

fof(f145,plain,(
    ! [X4,X2,X3] : k10_relat_1(k6_relat_1(X2),k2_xboole_0(X3,X4)) = k2_xboole_0(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),X4)) ),
    inference(resolution,[],[f78,f54])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1137,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f1136,f51])).

fof(f1136,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f104,f1092])).

fof(f1092,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f226,f1065])).

fof(f226,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f140,f51])).

fof(f140,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4))) ) ),
    inference(subsumption_resolution,[],[f139,f66])).

fof(f66,plain,(
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

fof(f139,plain,(
    ! [X4,X3] :
      ( k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k7_relat_1(X3,X4)) ) ),
    inference(subsumption_resolution,[],[f137,f68])).

fof(f137,plain,(
    ! [X4,X3] :
      ( k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k7_relat_1(X3,X4)) ) ),
    inference(superposition,[],[f60,f58])).

fof(f58,plain,(
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

fof(f60,plain,(
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

fof(f104,plain,(
    ! [X2,X1] :
      ( k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f57,f66])).

fof(f206,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k5_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X1),X2))
      | r1_tarski(X1,k10_relat_1(sK1,X2)) ) ),
    inference(superposition,[],[f94,f164])).

fof(f164,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK1,X1))) ),
    inference(resolution,[],[f95,f51])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f77,f90])).

fof(f77,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f91])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:54:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (23614)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.49  % (23606)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (23612)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.50  % (23627)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (23604)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (23624)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (23603)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (23605)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (23607)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (23621)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (23600)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (23618)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (23628)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (23615)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (23628)Refutation not found, incomplete strategy% (23628)------------------------------
% 0.21/0.53  % (23628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23628)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23628)Memory used [KB]: 10746
% 0.21/0.53  % (23628)Time elapsed: 0.123 s
% 0.21/0.53  % (23628)------------------------------
% 0.21/0.53  % (23628)------------------------------
% 0.21/0.53  % (23602)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (23601)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (23608)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (23616)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (23620)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (23611)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (23622)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (23629)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (23619)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (23616)Refutation not found, incomplete strategy% (23616)------------------------------
% 0.21/0.54  % (23616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23626)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (23613)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (23616)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23616)Memory used [KB]: 10618
% 0.21/0.54  % (23616)Time elapsed: 0.131 s
% 0.21/0.54  % (23616)------------------------------
% 0.21/0.54  % (23616)------------------------------
% 0.21/0.54  % (23617)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (23623)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (23609)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (23610)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (23625)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (23610)Refutation not found, incomplete strategy% (23610)------------------------------
% 0.21/0.55  % (23610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23610)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (23610)Memory used [KB]: 10746
% 0.21/0.55  % (23610)Time elapsed: 0.142 s
% 0.21/0.55  % (23610)------------------------------
% 0.21/0.55  % (23610)------------------------------
% 2.12/0.66  % (23622)Refutation found. Thanks to Tanya!
% 2.12/0.66  % SZS status Theorem for theBenchmark
% 2.12/0.66  % SZS output start Proof for theBenchmark
% 2.12/0.66  fof(f1179,plain,(
% 2.12/0.66    $false),
% 2.12/0.66    inference(subsumption_resolution,[],[f1178,f53])).
% 2.12/0.66  fof(f53,plain,(
% 2.12/0.66    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 2.12/0.66    inference(cnf_transformation,[],[f47])).
% 2.12/0.66  fof(f47,plain,(
% 2.12/0.66    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 2.12/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f46])).
% 2.12/0.66  fof(f46,plain,(
% 2.12/0.66    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 2.12/0.66    introduced(choice_axiom,[])).
% 2.12/0.66  fof(f32,plain,(
% 2.12/0.66    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 2.12/0.66    inference(flattening,[],[f31])).
% 2.12/0.66  fof(f31,plain,(
% 2.12/0.66    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.12/0.66    inference(ennf_transformation,[],[f29])).
% 2.12/0.66  fof(f29,negated_conjecture,(
% 2.12/0.66    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.12/0.66    inference(negated_conjecture,[],[f28])).
% 2.12/0.66  fof(f28,conjecture,(
% 2.12/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 2.12/0.66  fof(f1178,plain,(
% 2.12/0.66    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 2.12/0.66    inference(subsumption_resolution,[],[f1176,f154])).
% 2.12/0.66  fof(f154,plain,(
% 2.12/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f153,f96])).
% 2.12/0.66  fof(f96,plain,(
% 2.12/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.12/0.66    inference(equality_resolution,[],[f72])).
% 2.12/0.66  fof(f72,plain,(
% 2.12/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.12/0.66    inference(cnf_transformation,[],[f49])).
% 2.12/0.66  fof(f49,plain,(
% 2.12/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.12/0.66    inference(flattening,[],[f48])).
% 2.12/0.66  fof(f48,plain,(
% 2.12/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.12/0.66    inference(nnf_transformation,[],[f2])).
% 2.12/0.66  fof(f2,axiom,(
% 2.12/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.12/0.66  fof(f153,plain,(
% 2.12/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X0)) )),
% 2.12/0.66    inference(superposition,[],[f93,f92])).
% 2.12/0.66  fof(f92,plain,(
% 2.12/0.66    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.12/0.66    inference(definition_unfolding,[],[f61,f90])).
% 2.12/0.66  fof(f90,plain,(
% 2.12/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.12/0.66    inference(definition_unfolding,[],[f63,f89])).
% 2.12/0.66  fof(f89,plain,(
% 2.12/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.12/0.66    inference(definition_unfolding,[],[f64,f88])).
% 2.12/0.66  fof(f88,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.12/0.66    inference(definition_unfolding,[],[f76,f87])).
% 2.12/0.66  fof(f87,plain,(
% 2.12/0.66    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.12/0.66    inference(definition_unfolding,[],[f81,f86])).
% 2.12/0.66  fof(f86,plain,(
% 2.12/0.66    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.12/0.66    inference(definition_unfolding,[],[f82,f85])).
% 2.12/0.66  fof(f85,plain,(
% 2.12/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.12/0.66    inference(definition_unfolding,[],[f83,f84])).
% 2.12/0.66  fof(f84,plain,(
% 2.12/0.66    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f14])).
% 2.12/0.66  fof(f14,axiom,(
% 2.12/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.12/0.66  fof(f83,plain,(
% 2.12/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f13])).
% 2.12/0.66  fof(f13,axiom,(
% 2.12/0.66    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.12/0.66  fof(f82,plain,(
% 2.12/0.66    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f12])).
% 2.12/0.66  fof(f12,axiom,(
% 2.12/0.66    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.12/0.66  fof(f81,plain,(
% 2.12/0.66    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f11])).
% 2.12/0.66  fof(f11,axiom,(
% 2.12/0.66    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.12/0.66  fof(f76,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f10])).
% 2.12/0.66  fof(f10,axiom,(
% 2.12/0.66    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.12/0.66  fof(f64,plain,(
% 2.12/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f9])).
% 2.12/0.66  fof(f9,axiom,(
% 2.12/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.12/0.66  fof(f63,plain,(
% 2.12/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.12/0.66    inference(cnf_transformation,[],[f15])).
% 2.12/0.66  fof(f15,axiom,(
% 2.12/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.12/0.66  fof(f61,plain,(
% 2.12/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.12/0.66    inference(cnf_transformation,[],[f30])).
% 2.12/0.66  fof(f30,plain,(
% 2.12/0.66    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.12/0.66    inference(rectify,[],[f1])).
% 2.12/0.66  fof(f1,axiom,(
% 2.12/0.66    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.12/0.66  fof(f93,plain,(
% 2.12/0.66    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r1_tarski(X0,X1)) )),
% 2.12/0.66    inference(definition_unfolding,[],[f75,f91])).
% 2.12/0.66  fof(f91,plain,(
% 2.12/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.12/0.66    inference(definition_unfolding,[],[f65,f90])).
% 2.12/0.66  fof(f65,plain,(
% 2.12/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.12/0.66    inference(cnf_transformation,[],[f4])).
% 2.12/0.66  fof(f4,axiom,(
% 2.12/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.12/0.66  fof(f75,plain,(
% 2.12/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f50])).
% 2.12/0.66  fof(f50,plain,(
% 2.12/0.66    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.12/0.66    inference(nnf_transformation,[],[f3])).
% 2.12/0.66  fof(f3,axiom,(
% 2.12/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.12/0.66  fof(f1176,plain,(
% 2.12/0.66    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 2.12/0.66    inference(superposition,[],[f206,f1138])).
% 2.12/0.66  fof(f1138,plain,(
% 2.12/0.66    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 2.12/0.66    inference(forward_demodulation,[],[f1137,f1065])).
% 2.12/0.66  fof(f1065,plain,(
% 2.12/0.66    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 2.12/0.66    inference(subsumption_resolution,[],[f1061,f51])).
% 2.12/0.66  fof(f51,plain,(
% 2.12/0.66    v1_relat_1(sK1)),
% 2.12/0.66    inference(cnf_transformation,[],[f47])).
% 2.12/0.66  fof(f1061,plain,(
% 2.12/0.66    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 2.12/0.66    inference(resolution,[],[f1026,f118])).
% 2.12/0.66  fof(f118,plain,(
% 2.12/0.66    ( ! [X6,X7] : (~r1_tarski(X6,k1_relat_1(k7_relat_1(X7,X6))) | k1_relat_1(k7_relat_1(X7,X6)) = X6 | ~v1_relat_1(X7)) )),
% 2.12/0.66    inference(resolution,[],[f73,f68])).
% 2.12/0.66  fof(f68,plain,(
% 2.12/0.66    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f39])).
% 2.12/0.66  fof(f39,plain,(
% 2.12/0.66    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.12/0.66    inference(ennf_transformation,[],[f25])).
% 2.12/0.66  fof(f25,axiom,(
% 2.12/0.66    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 2.12/0.66  fof(f73,plain,(
% 2.12/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f49])).
% 2.12/0.66  fof(f1026,plain,(
% 2.12/0.66    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 2.12/0.66    inference(subsumption_resolution,[],[f1018,f51])).
% 2.12/0.66  fof(f1018,plain,(
% 2.12/0.66    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) | ~v1_relat_1(sK1)),
% 2.12/0.66    inference(superposition,[],[f1010,f69])).
% 2.12/0.66  fof(f69,plain,(
% 2.12/0.66    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f40])).
% 2.12/0.66  fof(f40,plain,(
% 2.12/0.66    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.12/0.66    inference(ennf_transformation,[],[f26])).
% 2.12/0.66  fof(f26,axiom,(
% 2.12/0.66    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.12/0.66  fof(f1010,plain,(
% 2.12/0.66    r1_tarski(sK0,k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),
% 2.12/0.66    inference(superposition,[],[f936,f106])).
% 2.12/0.66  fof(f106,plain,(
% 2.12/0.66    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 2.12/0.66    inference(forward_demodulation,[],[f105,f55])).
% 2.12/0.66  fof(f55,plain,(
% 2.12/0.66    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.12/0.66    inference(cnf_transformation,[],[f24])).
% 2.12/0.66  fof(f24,axiom,(
% 2.12/0.66    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.12/0.66  fof(f105,plain,(
% 2.12/0.66    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 2.12/0.66    inference(forward_demodulation,[],[f103,f56])).
% 2.12/0.66  fof(f56,plain,(
% 2.12/0.66    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.12/0.66    inference(cnf_transformation,[],[f24])).
% 2.12/0.66  fof(f103,plain,(
% 2.12/0.66    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 2.12/0.66    inference(resolution,[],[f57,f54])).
% 2.12/0.66  fof(f54,plain,(
% 2.12/0.66    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.12/0.66    inference(cnf_transformation,[],[f16])).
% 2.12/0.66  fof(f16,axiom,(
% 2.12/0.66    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 2.12/0.66  fof(f57,plain,(
% 2.12/0.66    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 2.12/0.66    inference(cnf_transformation,[],[f33])).
% 2.12/0.66  fof(f33,plain,(
% 2.12/0.66    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.12/0.66    inference(ennf_transformation,[],[f21])).
% 2.12/0.66  fof(f21,axiom,(
% 2.12/0.66    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 2.12/0.66  fof(f936,plain,(
% 2.12/0.66    ( ! [X17] : (r1_tarski(k10_relat_1(k6_relat_1(X17),sK0),k1_relat_1(k5_relat_1(k6_relat_1(X17),sK1)))) )),
% 2.12/0.66    inference(forward_demodulation,[],[f931,f135])).
% 2.12/0.66  fof(f135,plain,(
% 2.12/0.66    ( ! [X0] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) )),
% 2.12/0.66    inference(resolution,[],[f130,f54])).
% 2.12/0.66  fof(f130,plain,(
% 2.12/0.66    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1))) )),
% 2.12/0.66    inference(resolution,[],[f59,f51])).
% 2.12/0.66  fof(f59,plain,(
% 2.12/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f35])).
% 2.12/0.66  fof(f35,plain,(
% 2.12/0.66    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.12/0.66    inference(ennf_transformation,[],[f23])).
% 2.12/0.66  fof(f23,axiom,(
% 2.12/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 2.12/0.66  fof(f931,plain,(
% 2.12/0.66    ( ! [X17] : (r1_tarski(k10_relat_1(k6_relat_1(X17),sK0),k10_relat_1(k6_relat_1(X17),k1_relat_1(sK1)))) )),
% 2.12/0.66    inference(superposition,[],[f259,f896])).
% 2.12/0.66  fof(f896,plain,(
% 2.12/0.66    k1_relat_1(sK1) = k2_xboole_0(sK0,k1_relat_1(sK1))),
% 2.12/0.66    inference(resolution,[],[f891,f96])).
% 2.12/0.66  fof(f891,plain,(
% 2.12/0.66    ( ! [X71] : (~r1_tarski(k1_relat_1(sK1),X71) | k2_xboole_0(sK0,X71) = X71) )),
% 2.12/0.66    inference(resolution,[],[f219,f52])).
% 2.12/0.66  fof(f52,plain,(
% 2.12/0.66    r1_tarski(sK0,k1_relat_1(sK1))),
% 2.12/0.66    inference(cnf_transformation,[],[f47])).
% 2.12/0.66  fof(f219,plain,(
% 2.12/0.66    ( ! [X4,X5,X3] : (~r1_tarski(X3,X5) | k2_xboole_0(X3,X4) = X4 | ~r1_tarski(X5,X4)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f212,f96])).
% 2.12/0.66  fof(f212,plain,(
% 2.12/0.66    ( ! [X4,X5,X3] : (k2_xboole_0(X3,X4) = X4 | ~r1_tarski(X4,X4) | ~r1_tarski(X3,X5) | ~r1_tarski(X5,X4)) )),
% 2.12/0.66    inference(resolution,[],[f117,f124])).
% 2.12/0.66  fof(f124,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X2,X1),X1) | ~r1_tarski(X2,X0) | ~r1_tarski(X0,X1)) )),
% 2.12/0.66    inference(superposition,[],[f80,f70])).
% 2.12/0.66  fof(f70,plain,(
% 2.12/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f41])).
% 2.12/0.66  fof(f41,plain,(
% 2.12/0.66    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.12/0.66    inference(ennf_transformation,[],[f6])).
% 2.12/0.66  fof(f6,axiom,(
% 2.12/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.12/0.66  fof(f80,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f45])).
% 2.12/0.66  fof(f45,plain,(
% 2.12/0.66    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 2.12/0.66    inference(ennf_transformation,[],[f8])).
% 2.12/0.66  fof(f8,axiom,(
% 2.12/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).
% 2.12/0.66  fof(f117,plain,(
% 2.12/0.66    ( ! [X4,X5,X3] : (~r1_tarski(k2_xboole_0(X3,X4),X5) | k2_xboole_0(X3,X4) = X5 | ~r1_tarski(X5,X4)) )),
% 2.12/0.66    inference(resolution,[],[f73,f79])).
% 2.12/0.66  fof(f79,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f44])).
% 2.12/0.66  fof(f44,plain,(
% 2.12/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.12/0.66    inference(ennf_transformation,[],[f5])).
% 2.12/0.66  fof(f5,axiom,(
% 2.12/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.12/0.66  fof(f259,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k10_relat_1(k6_relat_1(X0),k2_xboole_0(X1,X2)))) )),
% 2.12/0.66    inference(superposition,[],[f62,f145])).
% 2.12/0.66  fof(f145,plain,(
% 2.12/0.66    ( ! [X4,X2,X3] : (k10_relat_1(k6_relat_1(X2),k2_xboole_0(X3,X4)) = k2_xboole_0(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),X4))) )),
% 2.12/0.66    inference(resolution,[],[f78,f54])).
% 2.12/0.66  fof(f78,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 2.12/0.66    inference(cnf_transformation,[],[f43])).
% 2.12/0.66  fof(f43,plain,(
% 2.12/0.66    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.12/0.66    inference(ennf_transformation,[],[f22])).
% 2.12/0.66  fof(f22,axiom,(
% 2.12/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 2.12/0.66  fof(f62,plain,(
% 2.12/0.66    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.12/0.66    inference(cnf_transformation,[],[f7])).
% 2.12/0.66  fof(f7,axiom,(
% 2.12/0.66    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.12/0.66  fof(f1137,plain,(
% 2.12/0.66    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 2.12/0.66    inference(subsumption_resolution,[],[f1136,f51])).
% 2.12/0.66  fof(f1136,plain,(
% 2.12/0.66    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 2.12/0.66    inference(superposition,[],[f104,f1092])).
% 2.12/0.66  fof(f1092,plain,(
% 2.12/0.66    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 2.12/0.66    inference(superposition,[],[f226,f1065])).
% 2.12/0.66  fof(f226,plain,(
% 2.12/0.66    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 2.12/0.66    inference(resolution,[],[f140,f51])).
% 2.12/0.66  fof(f140,plain,(
% 2.12/0.66    ( ! [X4,X3] : (~v1_relat_1(X3) | k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4)))) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f139,f66])).
% 2.12/0.66  fof(f66,plain,(
% 2.12/0.66    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f37])).
% 2.12/0.66  fof(f37,plain,(
% 2.12/0.66    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.12/0.66    inference(ennf_transformation,[],[f17])).
% 2.12/0.66  fof(f17,axiom,(
% 2.12/0.66    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.12/0.66  fof(f139,plain,(
% 2.12/0.66    ( ! [X4,X3] : (k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4))) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(X3,X4))) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f137,f68])).
% 2.12/0.66  fof(f137,plain,(
% 2.12/0.66    ( ! [X4,X3] : (k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4))) | ~r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X4) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(X3,X4))) )),
% 2.12/0.66    inference(superposition,[],[f60,f58])).
% 2.12/0.66  fof(f58,plain,(
% 2.12/0.66    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f34])).
% 2.12/0.66  fof(f34,plain,(
% 2.12/0.66    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.12/0.66    inference(ennf_transformation,[],[f18])).
% 2.12/0.66  fof(f18,axiom,(
% 2.12/0.66    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 2.12/0.66  fof(f60,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f36])).
% 2.12/0.66  fof(f36,plain,(
% 2.12/0.66    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 2.12/0.66    inference(ennf_transformation,[],[f19])).
% 2.12/0.66  fof(f19,axiom,(
% 2.12/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 2.12/0.66  fof(f104,plain,(
% 2.12/0.66    ( ! [X2,X1] : (k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2))) | ~v1_relat_1(X1)) )),
% 2.12/0.66    inference(resolution,[],[f57,f66])).
% 2.12/0.66  fof(f206,plain,(
% 2.12/0.66    ( ! [X2,X1] : (k1_xboole_0 != k5_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X1),X2)) | r1_tarski(X1,k10_relat_1(sK1,X2))) )),
% 2.12/0.66    inference(superposition,[],[f94,f164])).
% 2.12/0.66  fof(f164,plain,(
% 2.12/0.66    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK1,X1)))) )),
% 2.12/0.66    inference(resolution,[],[f95,f51])).
% 2.12/0.66  fof(f95,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 2.12/0.66    inference(definition_unfolding,[],[f77,f90])).
% 2.12/0.66  fof(f77,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f42])).
% 2.12/0.66  fof(f42,plain,(
% 2.12/0.66    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.12/0.66    inference(ennf_transformation,[],[f27])).
% 2.12/0.66  fof(f27,axiom,(
% 2.12/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 2.12/0.66  fof(f94,plain,(
% 2.12/0.66    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r1_tarski(X0,X1)) )),
% 2.12/0.66    inference(definition_unfolding,[],[f74,f91])).
% 2.12/0.66  fof(f74,plain,(
% 2.12/0.66    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.12/0.66    inference(cnf_transformation,[],[f50])).
% 2.12/0.66  % SZS output end Proof for theBenchmark
% 2.12/0.66  % (23622)------------------------------
% 2.12/0.66  % (23622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.66  % (23622)Termination reason: Refutation
% 2.12/0.66  
% 2.12/0.66  % (23622)Memory used [KB]: 7419
% 2.12/0.66  % (23622)Time elapsed: 0.257 s
% 2.12/0.66  % (23622)------------------------------
% 2.12/0.66  % (23622)------------------------------
% 2.12/0.66  % (23597)Success in time 0.295 s
%------------------------------------------------------------------------------
