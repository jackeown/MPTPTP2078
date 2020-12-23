%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:23 EST 2020

% Result     : Theorem 2.97s
% Output     : Refutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  109 (1469 expanded)
%              Number of leaves         :   18 ( 469 expanded)
%              Depth                    :   22
%              Number of atoms          :  187 (1986 expanded)
%              Number of equality atoms :   89 (1224 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2659,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2542,f1516])).

fof(f1516,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(subsumption_resolution,[],[f1503,f1399])).

fof(f1399,plain,(
    ! [X2,X3] : r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k7_relat_1(k6_relat_1(X3),X2)) ),
    inference(superposition,[],[f1348,f1117])).

fof(f1117,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(superposition,[],[f235,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(resolution,[],[f81,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(forward_demodulation,[],[f72,f67])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f235,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k7_relat_1(k6_relat_1(X3),k4_xboole_0(X4,k4_xboole_0(X4,X3))) ),
    inference(forward_demodulation,[],[f229,f67])).

fof(f229,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k7_relat_1(k6_relat_1(X3),k1_setfam_1(k1_enumset1(X4,X4,X3))) ),
    inference(superposition,[],[f140,f101])).

fof(f101,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(superposition,[],[f67,f66])).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f47,f48,f48])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f140,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f137,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f137,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) ),
    inference(resolution,[],[f79,f39])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) ) ),
    inference(forward_demodulation,[],[f70,f67])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f54,f63])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f1348,plain,(
    ! [X4,X2,X3] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X2),k7_relat_1(k6_relat_1(X3),X2)) ),
    inference(subsumption_resolution,[],[f1345,f1268])).

fof(f1268,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[],[f127,f327])).

fof(f327,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k4_xboole_0(k6_relat_1(X0),k4_xboole_0(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(forward_demodulation,[],[f319,f94])).

fof(f94,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f53,f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f319,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k4_xboole_0(k6_relat_1(X0),k4_xboole_0(k6_relat_1(X0),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) ),
    inference(resolution,[],[f105,f39])).

fof(f105,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k5_relat_1(X3,k6_relat_1(X4)) = k4_xboole_0(X3,k4_xboole_0(X3,k5_relat_1(X3,k6_relat_1(X4)))) ) ),
    inference(forward_demodulation,[],[f103,f67])).

fof(f103,plain,(
    ! [X4,X3] :
      ( k5_relat_1(X3,k6_relat_1(X4)) = k1_setfam_1(k1_enumset1(X3,X3,k5_relat_1(X3,k6_relat_1(X4))))
      | ~ v1_relat_1(X3) ) ),
    inference(backward_demodulation,[],[f99,f101])).

fof(f99,plain,(
    ! [X4,X3] :
      ( k5_relat_1(X3,k6_relat_1(X4)) = k4_xboole_0(k5_relat_1(X3,k6_relat_1(X4)),k4_xboole_0(k5_relat_1(X3,k6_relat_1(X4)),X3))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f80,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(forward_demodulation,[],[f71,f67])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f63])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f127,plain,(
    ! [X0,X1] : v1_relat_1(k4_xboole_0(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f115,f39])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f78,f77])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f68,f67])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f69,f67])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f1345,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X2),k7_relat_1(k6_relat_1(X3),X2))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) ) ),
    inference(backward_demodulation,[],[f507,f1322])).

fof(f1322,plain,(
    ! [X6,X4,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X6) = k5_relat_1(k6_relat_1(X6),k7_relat_1(k6_relat_1(X4),X5)) ),
    inference(resolution,[],[f1268,f53])).

fof(f507,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X4),X3)),k7_relat_1(k6_relat_1(X3),X2))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) ) ),
    inference(forward_demodulation,[],[f506,f94])).

fof(f506,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X2))
      | r1_tarski(k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))),k7_relat_1(k6_relat_1(X3),X2)) ) ),
    inference(subsumption_resolution,[],[f505,f39])).

fof(f505,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X2))
      | r1_tarski(k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))),k7_relat_1(k6_relat_1(X3),X2))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f499,f39])).

fof(f499,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X2))
      | r1_tarski(k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))),k7_relat_1(k6_relat_1(X3),X2))
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f181,f94])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(k5_relat_1(X0,X1))
      | r1_tarski(k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f177,f39])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f55,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f1503,plain,(
    ! [X2,X3] :
      ( k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k7_relat_1(k6_relat_1(X3),X2)) ) ),
    inference(resolution,[],[f1399,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f2542,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(superposition,[],[f96,f1762])).

fof(f1762,plain,(
    ! [X14,X13] : k7_relat_1(k6_relat_1(X14),X13) = k6_relat_1(k4_xboole_0(X13,k4_xboole_0(X13,X14))) ),
    inference(forward_demodulation,[],[f1761,f359])).

fof(f359,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) ),
    inference(superposition,[],[f144,f97])).

fof(f97,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(resolution,[],[f80,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1761,plain,(
    ! [X14,X13] : k6_relat_1(k4_xboole_0(X13,k4_xboole_0(X13,X14))) = k7_relat_1(k7_relat_1(k6_relat_1(X14),X13),X13) ),
    inference(forward_demodulation,[],[f1760,f1117])).

fof(f1760,plain,(
    ! [X14,X13] : k6_relat_1(k4_xboole_0(X13,k4_xboole_0(X13,X14))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X14),X13),X14),X13) ),
    inference(forward_demodulation,[],[f1759,f144])).

fof(f1759,plain,(
    ! [X14,X13] : k6_relat_1(k4_xboole_0(X13,k4_xboole_0(X13,X14))) = k7_relat_1(k7_relat_1(k6_relat_1(X14),k4_xboole_0(X13,k4_xboole_0(X13,X14))),X13) ),
    inference(forward_demodulation,[],[f1719,f1516])).

fof(f1719,plain,(
    ! [X14,X13] : k6_relat_1(k4_xboole_0(X13,k4_xboole_0(X13,X14))) = k7_relat_1(k7_relat_1(k6_relat_1(k4_xboole_0(X13,k4_xboole_0(X13,X14))),X14),X13) ),
    inference(superposition,[],[f373,f182])).

fof(f182,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(superposition,[],[f94,f84])).

fof(f84,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f82,f42])).

fof(f42,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) ),
    inference(resolution,[],[f43,f39])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f373,plain,(
    ! [X6,X7,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),X6) = k7_relat_1(k6_relat_1(X7),k4_xboole_0(X6,k4_xboole_0(X6,X5))) ),
    inference(forward_demodulation,[],[f361,f67])).

fof(f361,plain,(
    ! [X6,X7,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),X6) = k7_relat_1(k6_relat_1(X7),k1_setfam_1(k1_enumset1(X6,X6,X5))) ),
    inference(superposition,[],[f144,f101])).

fof(f96,plain,(
    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f75,f94])).

fof(f75,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f64,f67])).

fof(f64,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f38,f63])).

fof(f38,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f34])).

fof(f34,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n011.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 20:30:42 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.20/0.51  % (3186)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (3188)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (3174)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (3175)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (3175)Refutation not found, incomplete strategy% (3175)------------------------------
% 0.20/0.52  % (3175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3175)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (3175)Memory used [KB]: 1663
% 0.20/0.52  % (3175)Time elapsed: 0.114 s
% 0.20/0.52  % (3175)------------------------------
% 0.20/0.52  % (3175)------------------------------
% 0.20/0.52  % (3197)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (3188)Refutation not found, incomplete strategy% (3188)------------------------------
% 0.20/0.53  % (3188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3188)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  % (3177)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  
% 0.20/0.53  % (3188)Memory used [KB]: 1663
% 0.20/0.53  % (3188)Time elapsed: 0.058 s
% 0.20/0.53  % (3188)------------------------------
% 0.20/0.53  % (3188)------------------------------
% 0.20/0.53  % (3176)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (3178)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (3180)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (3179)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (3191)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (3204)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (3204)Refutation not found, incomplete strategy% (3204)------------------------------
% 0.20/0.53  % (3204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3204)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3204)Memory used [KB]: 1663
% 0.20/0.53  % (3204)Time elapsed: 0.001 s
% 0.20/0.53  % (3204)------------------------------
% 0.20/0.53  % (3204)------------------------------
% 0.20/0.53  % (3186)Refutation not found, incomplete strategy% (3186)------------------------------
% 0.20/0.53  % (3186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3186)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3186)Memory used [KB]: 10618
% 0.20/0.53  % (3186)Time elapsed: 0.125 s
% 0.20/0.53  % (3186)------------------------------
% 0.20/0.53  % (3186)------------------------------
% 0.20/0.53  % (3189)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (3199)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (3181)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (3201)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (3195)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (3202)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (3190)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (3194)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (3187)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (3192)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (3190)Refutation not found, incomplete strategy% (3190)------------------------------
% 0.20/0.54  % (3190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (3190)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (3190)Memory used [KB]: 10618
% 0.20/0.54  % (3190)Time elapsed: 0.139 s
% 0.20/0.54  % (3190)------------------------------
% 0.20/0.54  % (3190)------------------------------
% 0.20/0.54  % (3192)Refutation not found, incomplete strategy% (3192)------------------------------
% 0.20/0.54  % (3192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (3192)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (3192)Memory used [KB]: 1663
% 0.20/0.54  % (3192)Time elapsed: 0.139 s
% 0.20/0.54  % (3192)------------------------------
% 0.20/0.54  % (3192)------------------------------
% 0.20/0.54  % (3182)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (3183)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (3185)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (3191)Refutation not found, incomplete strategy% (3191)------------------------------
% 0.20/0.54  % (3191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (3191)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (3191)Memory used [KB]: 1663
% 0.20/0.54  % (3191)Time elapsed: 0.124 s
% 0.20/0.54  % (3191)------------------------------
% 0.20/0.54  % (3191)------------------------------
% 0.20/0.54  % (3185)Refutation not found, incomplete strategy% (3185)------------------------------
% 0.20/0.54  % (3185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (3201)Refutation not found, incomplete strategy% (3201)------------------------------
% 0.20/0.54  % (3201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (3185)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (3185)Memory used [KB]: 6140
% 0.20/0.54  % (3185)Time elapsed: 0.140 s
% 0.20/0.54  % (3185)------------------------------
% 0.20/0.54  % (3185)------------------------------
% 0.20/0.54  % (3201)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (3201)Memory used [KB]: 6140
% 0.20/0.54  % (3201)Time elapsed: 0.138 s
% 0.20/0.54  % (3201)------------------------------
% 0.20/0.54  % (3201)------------------------------
% 0.20/0.55  % (3193)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (3198)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (3199)Refutation not found, incomplete strategy% (3199)------------------------------
% 0.20/0.55  % (3199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (3199)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (3199)Memory used [KB]: 6140
% 0.20/0.55  % (3199)Time elapsed: 0.147 s
% 0.20/0.55  % (3199)------------------------------
% 0.20/0.55  % (3199)------------------------------
% 0.20/0.55  % (3198)Refutation not found, incomplete strategy% (3198)------------------------------
% 0.20/0.55  % (3198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (3198)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (3198)Memory used [KB]: 10618
% 0.20/0.55  % (3198)Time elapsed: 0.147 s
% 0.20/0.55  % (3198)------------------------------
% 0.20/0.55  % (3198)------------------------------
% 0.20/0.55  % (3184)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (3184)Refutation not found, incomplete strategy% (3184)------------------------------
% 0.20/0.55  % (3184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (3184)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (3184)Memory used [KB]: 10618
% 0.20/0.55  % (3184)Time elapsed: 0.144 s
% 0.20/0.55  % (3184)------------------------------
% 0.20/0.55  % (3184)------------------------------
% 0.20/0.55  % (3202)Refutation not found, incomplete strategy% (3202)------------------------------
% 0.20/0.55  % (3202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (3202)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (3202)Memory used [KB]: 6140
% 0.20/0.55  % (3202)Time elapsed: 0.149 s
% 0.20/0.55  % (3202)------------------------------
% 0.20/0.55  % (3202)------------------------------
% 0.20/0.55  % (3203)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.58/0.55  % (3203)Refutation not found, incomplete strategy% (3203)------------------------------
% 1.58/0.55  % (3203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.55  % (3203)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.55  
% 1.58/0.55  % (3203)Memory used [KB]: 10618
% 1.58/0.55  % (3203)Time elapsed: 0.146 s
% 1.58/0.55  % (3203)------------------------------
% 1.58/0.55  % (3203)------------------------------
% 1.58/0.55  % (3196)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.04/0.65  % (3285)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.04/0.65  % (3284)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.20/0.65  % (3278)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.20/0.65  % (3284)Refutation not found, incomplete strategy% (3284)------------------------------
% 2.20/0.65  % (3284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.66  % (3284)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.66  
% 2.20/0.66  % (3284)Memory used [KB]: 10618
% 2.20/0.66  % (3284)Time elapsed: 0.049 s
% 2.20/0.66  % (3284)------------------------------
% 2.20/0.66  % (3284)------------------------------
% 2.20/0.66  % (3176)Refutation not found, incomplete strategy% (3176)------------------------------
% 2.20/0.66  % (3176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.66  % (3176)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.66  
% 2.20/0.66  % (3176)Memory used [KB]: 6140
% 2.20/0.66  % (3176)Time elapsed: 0.254 s
% 2.20/0.66  % (3176)------------------------------
% 2.20/0.66  % (3176)------------------------------
% 2.20/0.67  % (3281)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.20/0.67  % (3281)Refutation not found, incomplete strategy% (3281)------------------------------
% 2.20/0.67  % (3281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.67  % (3281)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.67  
% 2.20/0.67  % (3281)Memory used [KB]: 10618
% 2.20/0.67  % (3281)Time elapsed: 0.101 s
% 2.20/0.67  % (3281)------------------------------
% 2.20/0.67  % (3281)------------------------------
% 2.20/0.67  % (3282)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.20/0.67  % (3288)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.20/0.67  % (3282)Refutation not found, incomplete strategy% (3282)------------------------------
% 2.20/0.67  % (3282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.67  % (3282)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.67  
% 2.20/0.67  % (3282)Memory used [KB]: 10618
% 2.20/0.67  % (3282)Time elapsed: 0.101 s
% 2.20/0.67  % (3282)------------------------------
% 2.20/0.67  % (3282)------------------------------
% 2.20/0.67  % (3279)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.20/0.67  % (3177)Refutation not found, incomplete strategy% (3177)------------------------------
% 2.20/0.67  % (3177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.67  % (3177)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.67  
% 2.20/0.67  % (3177)Memory used [KB]: 6140
% 2.20/0.67  % (3177)Time elapsed: 0.247 s
% 2.20/0.67  % (3177)------------------------------
% 2.20/0.67  % (3177)------------------------------
% 2.20/0.68  % (3289)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.20/0.68  % (3189)Refutation not found, incomplete strategy% (3189)------------------------------
% 2.20/0.68  % (3189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.68  % (3286)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.20/0.68  % (3283)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.20/0.68  % (3287)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.20/0.68  % (3291)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.20/0.68  % (3287)Refutation not found, incomplete strategy% (3287)------------------------------
% 2.20/0.68  % (3287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.68  % (3287)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.68  
% 2.20/0.68  % (3287)Memory used [KB]: 10618
% 2.20/0.68  % (3287)Time elapsed: 0.104 s
% 2.20/0.68  % (3287)------------------------------
% 2.20/0.68  % (3287)------------------------------
% 2.20/0.68  % (3291)Refutation not found, incomplete strategy% (3291)------------------------------
% 2.20/0.68  % (3291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.68  % (3291)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.68  
% 2.20/0.68  % (3291)Memory used [KB]: 10618
% 2.20/0.68  % (3291)Time elapsed: 0.099 s
% 2.20/0.68  % (3291)------------------------------
% 2.20/0.68  % (3291)------------------------------
% 2.20/0.68  % (3280)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.20/0.68  % (3283)Refutation not found, incomplete strategy% (3283)------------------------------
% 2.20/0.68  % (3283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.68  % (3182)Refutation not found, incomplete strategy% (3182)------------------------------
% 2.20/0.68  % (3182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.68  % (3182)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.68  
% 2.20/0.68  % (3182)Memory used [KB]: 6140
% 2.20/0.68  % (3182)Time elapsed: 0.280 s
% 2.20/0.68  % (3182)------------------------------
% 2.20/0.68  % (3182)------------------------------
% 2.20/0.68  % (3283)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.68  
% 2.20/0.68  % (3283)Memory used [KB]: 1663
% 2.20/0.68  % (3283)Time elapsed: 0.110 s
% 2.20/0.68  % (3283)------------------------------
% 2.20/0.68  % (3283)------------------------------
% 2.20/0.69  % (3189)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.69  
% 2.20/0.69  % (3189)Memory used [KB]: 6140
% 2.20/0.69  % (3189)Time elapsed: 0.269 s
% 2.20/0.69  % (3189)------------------------------
% 2.20/0.69  % (3189)------------------------------
% 2.20/0.69  % (3289)Refutation not found, incomplete strategy% (3289)------------------------------
% 2.20/0.69  % (3289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.69  % (3289)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.69  
% 2.20/0.69  % (3289)Memory used [KB]: 10618
% 2.20/0.69  % (3289)Time elapsed: 0.111 s
% 2.20/0.69  % (3289)------------------------------
% 2.20/0.69  % (3289)------------------------------
% 2.20/0.69  % (3290)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.97/0.77  % (3292)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 2.97/0.78  % (3296)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 2.97/0.79  % (3301)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 2.97/0.80  % (3293)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.97/0.80  % (3294)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 2.97/0.81  % (3196)Refutation found. Thanks to Tanya!
% 2.97/0.81  % SZS status Theorem for theBenchmark
% 2.97/0.81  % SZS output start Proof for theBenchmark
% 2.97/0.81  fof(f2659,plain,(
% 2.97/0.81    $false),
% 2.97/0.81    inference(subsumption_resolution,[],[f2542,f1516])).
% 2.97/0.81  fof(f1516,plain,(
% 2.97/0.81    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 2.97/0.81    inference(subsumption_resolution,[],[f1503,f1399])).
% 2.97/0.81  fof(f1399,plain,(
% 2.97/0.81    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k7_relat_1(k6_relat_1(X3),X2))) )),
% 2.97/0.81    inference(superposition,[],[f1348,f1117])).
% 2.97/0.81  fof(f1117,plain,(
% 2.97/0.81    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)) )),
% 2.97/0.81    inference(superposition,[],[f235,f144])).
% 2.97/0.81  fof(f144,plain,(
% 2.97/0.81    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 2.97/0.81    inference(resolution,[],[f81,f39])).
% 2.97/0.81  fof(f39,plain,(
% 2.97/0.81    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.97/0.81    inference(cnf_transformation,[],[f19])).
% 2.97/0.81  fof(f19,axiom,(
% 2.97/0.81    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.97/0.81  fof(f81,plain,(
% 2.97/0.81    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.97/0.81    inference(forward_demodulation,[],[f72,f67])).
% 2.97/0.81  fof(f67,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.97/0.81    inference(definition_unfolding,[],[f50,f63])).
% 2.97/0.81  fof(f63,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.97/0.81    inference(definition_unfolding,[],[f49,f48])).
% 2.97/0.81  fof(f48,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.97/0.81    inference(cnf_transformation,[],[f7])).
% 2.97/0.81  fof(f7,axiom,(
% 2.97/0.81    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.97/0.81  fof(f49,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.97/0.81    inference(cnf_transformation,[],[f8])).
% 2.97/0.81  fof(f8,axiom,(
% 2.97/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.97/0.81  fof(f50,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.97/0.81    inference(cnf_transformation,[],[f5])).
% 2.97/0.81  fof(f5,axiom,(
% 2.97/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.97/0.81  fof(f72,plain,(
% 2.97/0.81    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 2.97/0.81    inference(definition_unfolding,[],[f62,f63])).
% 2.97/0.81  fof(f62,plain,(
% 2.97/0.81    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 2.97/0.81    inference(cnf_transformation,[],[f33])).
% 2.97/0.81  fof(f33,plain,(
% 2.97/0.81    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 2.97/0.81    inference(ennf_transformation,[],[f10])).
% 2.97/0.81  fof(f10,axiom,(
% 2.97/0.81    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 2.97/0.81  fof(f235,plain,(
% 2.97/0.81    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k7_relat_1(k6_relat_1(X3),k4_xboole_0(X4,k4_xboole_0(X4,X3)))) )),
% 2.97/0.81    inference(forward_demodulation,[],[f229,f67])).
% 2.97/0.81  fof(f229,plain,(
% 2.97/0.81    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k7_relat_1(k6_relat_1(X3),k1_setfam_1(k1_enumset1(X4,X4,X3)))) )),
% 2.97/0.81    inference(superposition,[],[f140,f101])).
% 2.97/0.81  fof(f101,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0))) )),
% 2.97/0.81    inference(superposition,[],[f67,f66])).
% 2.97/0.81  fof(f66,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.97/0.81    inference(definition_unfolding,[],[f47,f48,f48])).
% 2.97/0.81  fof(f47,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.97/0.81    inference(cnf_transformation,[],[f6])).
% 2.97/0.81  fof(f6,axiom,(
% 2.97/0.81    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.97/0.81  fof(f140,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.97/0.81    inference(forward_demodulation,[],[f137,f41])).
% 2.97/0.81  fof(f41,plain,(
% 2.97/0.81    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.97/0.81    inference(cnf_transformation,[],[f13])).
% 2.97/0.81  fof(f13,axiom,(
% 2.97/0.81    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.97/0.81  fof(f137,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)))) )),
% 2.97/0.81    inference(resolution,[],[f79,f39])).
% 2.97/0.81  fof(f79,plain,(
% 2.97/0.81    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)))) )),
% 2.97/0.81    inference(forward_demodulation,[],[f70,f67])).
% 2.97/0.81  fof(f70,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 2.97/0.81    inference(definition_unfolding,[],[f54,f63])).
% 2.97/0.81  fof(f54,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.97/0.81    inference(cnf_transformation,[],[f28])).
% 2.97/0.81  fof(f28,plain,(
% 2.97/0.81    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.97/0.81    inference(ennf_transformation,[],[f11])).
% 2.97/0.81  fof(f11,axiom,(
% 2.97/0.81    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 2.97/0.81  fof(f1348,plain,(
% 2.97/0.81    ( ! [X4,X2,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X2),k7_relat_1(k6_relat_1(X3),X2))) )),
% 2.97/0.81    inference(subsumption_resolution,[],[f1345,f1268])).
% 2.97/0.81  fof(f1268,plain,(
% 2.97/0.81    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 2.97/0.81    inference(superposition,[],[f127,f327])).
% 2.97/0.81  fof(f327,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k4_xboole_0(k6_relat_1(X0),k4_xboole_0(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X0)))) )),
% 2.97/0.81    inference(forward_demodulation,[],[f319,f94])).
% 2.97/0.81  fof(f94,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.97/0.81    inference(resolution,[],[f53,f39])).
% 2.97/0.81  fof(f53,plain,(
% 2.97/0.81    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.97/0.81    inference(cnf_transformation,[],[f27])).
% 2.97/0.81  fof(f27,plain,(
% 2.97/0.81    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.97/0.81    inference(ennf_transformation,[],[f18])).
% 2.97/0.81  fof(f18,axiom,(
% 2.97/0.81    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 2.97/0.81  fof(f319,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k4_xboole_0(k6_relat_1(X0),k4_xboole_0(k6_relat_1(X0),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))))) )),
% 2.97/0.81    inference(resolution,[],[f105,f39])).
% 2.97/0.81  fof(f105,plain,(
% 2.97/0.81    ( ! [X4,X3] : (~v1_relat_1(X3) | k5_relat_1(X3,k6_relat_1(X4)) = k4_xboole_0(X3,k4_xboole_0(X3,k5_relat_1(X3,k6_relat_1(X4))))) )),
% 2.97/0.81    inference(forward_demodulation,[],[f103,f67])).
% 2.97/0.81  fof(f103,plain,(
% 2.97/0.81    ( ! [X4,X3] : (k5_relat_1(X3,k6_relat_1(X4)) = k1_setfam_1(k1_enumset1(X3,X3,k5_relat_1(X3,k6_relat_1(X4)))) | ~v1_relat_1(X3)) )),
% 2.97/0.81    inference(backward_demodulation,[],[f99,f101])).
% 2.97/0.81  fof(f99,plain,(
% 2.97/0.81    ( ! [X4,X3] : (k5_relat_1(X3,k6_relat_1(X4)) = k4_xboole_0(k5_relat_1(X3,k6_relat_1(X4)),k4_xboole_0(k5_relat_1(X3,k6_relat_1(X4)),X3)) | ~v1_relat_1(X3)) )),
% 2.97/0.81    inference(resolution,[],[f80,f55])).
% 2.97/0.81  fof(f55,plain,(
% 2.97/0.81    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 2.97/0.81    inference(cnf_transformation,[],[f29])).
% 2.97/0.81  fof(f29,plain,(
% 2.97/0.81    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 2.97/0.81    inference(ennf_transformation,[],[f14])).
% 2.97/0.81  fof(f14,axiom,(
% 2.97/0.81    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 2.97/0.81  fof(f80,plain,(
% 2.97/0.81    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 2.97/0.81    inference(forward_demodulation,[],[f71,f67])).
% 2.97/0.81  fof(f71,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.97/0.81    inference(definition_unfolding,[],[f58,f63])).
% 2.97/0.81  fof(f58,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.97/0.81    inference(cnf_transformation,[],[f32])).
% 2.97/0.81  fof(f32,plain,(
% 2.97/0.81    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.97/0.81    inference(ennf_transformation,[],[f3])).
% 2.97/0.81  fof(f3,axiom,(
% 2.97/0.81    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.97/0.81  fof(f127,plain,(
% 2.97/0.81    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(k6_relat_1(X0),X1))) )),
% 2.97/0.81    inference(resolution,[],[f115,f39])).
% 2.97/0.81  fof(f115,plain,(
% 2.97/0.81    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k4_xboole_0(X0,X1))) )),
% 2.97/0.81    inference(superposition,[],[f78,f77])).
% 2.97/0.81  fof(f77,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.97/0.81    inference(forward_demodulation,[],[f68,f67])).
% 2.97/0.81  fof(f68,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 2.97/0.81    inference(definition_unfolding,[],[f51,f63])).
% 2.97/0.81  fof(f51,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.97/0.81    inference(cnf_transformation,[],[f4])).
% 2.97/0.81  fof(f4,axiom,(
% 2.97/0.81    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.97/0.81  fof(f78,plain,(
% 2.97/0.81    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_relat_1(X0)) )),
% 2.97/0.81    inference(forward_demodulation,[],[f69,f67])).
% 2.97/0.81  fof(f69,plain,(
% 2.97/0.81    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 2.97/0.81    inference(definition_unfolding,[],[f52,f63])).
% 2.97/0.81  fof(f52,plain,(
% 2.97/0.81    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.97/0.81    inference(cnf_transformation,[],[f26])).
% 2.97/0.81  fof(f26,plain,(
% 2.97/0.81    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 2.97/0.81    inference(ennf_transformation,[],[f9])).
% 2.97/0.81  fof(f9,axiom,(
% 2.97/0.81    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 2.97/0.81  fof(f1345,plain,(
% 2.97/0.81    ( ! [X4,X2,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X2),k7_relat_1(k6_relat_1(X3),X2)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X2))) )),
% 2.97/0.81    inference(backward_demodulation,[],[f507,f1322])).
% 2.97/0.81  fof(f1322,plain,(
% 2.97/0.81    ( ! [X6,X4,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X6) = k5_relat_1(k6_relat_1(X6),k7_relat_1(k6_relat_1(X4),X5))) )),
% 2.97/0.81    inference(resolution,[],[f1268,f53])).
% 2.97/0.81  fof(f507,plain,(
% 2.97/0.81    ( ! [X4,X2,X3] : (r1_tarski(k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X4),X3)),k7_relat_1(k6_relat_1(X3),X2)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X2))) )),
% 2.97/0.81    inference(forward_demodulation,[],[f506,f94])).
% 2.97/0.81  fof(f506,plain,(
% 2.97/0.81    ( ! [X4,X2,X3] : (~v1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) | r1_tarski(k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))),k7_relat_1(k6_relat_1(X3),X2))) )),
% 2.97/0.81    inference(subsumption_resolution,[],[f505,f39])).
% 2.97/0.81  fof(f505,plain,(
% 2.97/0.81    ( ! [X4,X2,X3] : (~v1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) | r1_tarski(k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))),k7_relat_1(k6_relat_1(X3),X2)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 2.97/0.81    inference(subsumption_resolution,[],[f499,f39])).
% 2.97/0.81  fof(f499,plain,(
% 2.97/0.81    ( ! [X4,X2,X3] : (~v1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) | r1_tarski(k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))),k7_relat_1(k6_relat_1(X3),X2)) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 2.97/0.81    inference(superposition,[],[f181,f94])).
% 2.97/0.81  fof(f181,plain,(
% 2.97/0.81    ( ! [X2,X0,X1] : (~v1_relat_1(k5_relat_1(X0,X1)) | r1_tarski(k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))),k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.97/0.81    inference(subsumption_resolution,[],[f177,f39])).
% 2.97/0.81  fof(f177,plain,(
% 2.97/0.81    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.97/0.81    inference(superposition,[],[f55,f45])).
% 2.97/0.81  fof(f45,plain,(
% 2.97/0.81    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.97/0.81    inference(cnf_transformation,[],[f25])).
% 2.97/0.81  fof(f25,plain,(
% 2.97/0.81    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.97/0.81    inference(ennf_transformation,[],[f12])).
% 2.97/0.81  fof(f12,axiom,(
% 2.97/0.81    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 2.97/0.81  fof(f1503,plain,(
% 2.97/0.81    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) | ~r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k7_relat_1(k6_relat_1(X3),X2))) )),
% 2.97/0.81    inference(resolution,[],[f1399,f61])).
% 2.97/0.81  fof(f61,plain,(
% 2.97/0.81    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.97/0.81    inference(cnf_transformation,[],[f37])).
% 2.97/0.81  fof(f37,plain,(
% 2.97/0.81    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.97/0.81    inference(flattening,[],[f36])).
% 2.97/0.81  fof(f36,plain,(
% 2.97/0.81    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.97/0.81    inference(nnf_transformation,[],[f1])).
% 2.97/0.81  fof(f1,axiom,(
% 2.97/0.81    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.97/0.81  fof(f2542,plain,(
% 2.97/0.81    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0)),
% 2.97/0.81    inference(superposition,[],[f96,f1762])).
% 2.97/0.81  fof(f1762,plain,(
% 2.97/0.81    ( ! [X14,X13] : (k7_relat_1(k6_relat_1(X14),X13) = k6_relat_1(k4_xboole_0(X13,k4_xboole_0(X13,X14)))) )),
% 2.97/0.81    inference(forward_demodulation,[],[f1761,f359])).
% 2.97/0.81  fof(f359,plain,(
% 2.97/0.81    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) )),
% 2.97/0.81    inference(superposition,[],[f144,f97])).
% 2.97/0.81  fof(f97,plain,(
% 2.97/0.81    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.97/0.81    inference(resolution,[],[f80,f73])).
% 2.97/0.81  fof(f73,plain,(
% 2.97/0.81    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.97/0.81    inference(equality_resolution,[],[f60])).
% 2.97/0.81  fof(f60,plain,(
% 2.97/0.81    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.97/0.81    inference(cnf_transformation,[],[f37])).
% 2.97/0.81  fof(f1761,plain,(
% 2.97/0.81    ( ! [X14,X13] : (k6_relat_1(k4_xboole_0(X13,k4_xboole_0(X13,X14))) = k7_relat_1(k7_relat_1(k6_relat_1(X14),X13),X13)) )),
% 2.97/0.81    inference(forward_demodulation,[],[f1760,f1117])).
% 2.97/0.81  fof(f1760,plain,(
% 2.97/0.81    ( ! [X14,X13] : (k6_relat_1(k4_xboole_0(X13,k4_xboole_0(X13,X14))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X14),X13),X14),X13)) )),
% 2.97/0.81    inference(forward_demodulation,[],[f1759,f144])).
% 2.97/0.81  fof(f1759,plain,(
% 2.97/0.81    ( ! [X14,X13] : (k6_relat_1(k4_xboole_0(X13,k4_xboole_0(X13,X14))) = k7_relat_1(k7_relat_1(k6_relat_1(X14),k4_xboole_0(X13,k4_xboole_0(X13,X14))),X13)) )),
% 2.97/0.81    inference(forward_demodulation,[],[f1719,f1516])).
% 2.97/0.81  fof(f1719,plain,(
% 2.97/0.81    ( ! [X14,X13] : (k6_relat_1(k4_xboole_0(X13,k4_xboole_0(X13,X14))) = k7_relat_1(k7_relat_1(k6_relat_1(k4_xboole_0(X13,k4_xboole_0(X13,X14))),X14),X13)) )),
% 2.97/0.81    inference(superposition,[],[f373,f182])).
% 2.97/0.81  fof(f182,plain,(
% 2.97/0.81    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 2.97/0.81    inference(superposition,[],[f94,f84])).
% 2.97/0.81  fof(f84,plain,(
% 2.97/0.81    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 2.97/0.81    inference(forward_demodulation,[],[f82,f42])).
% 2.97/0.81  fof(f42,plain,(
% 2.97/0.81    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.97/0.81    inference(cnf_transformation,[],[f13])).
% 2.97/0.81  fof(f82,plain,(
% 2.97/0.81    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) )),
% 2.97/0.81    inference(resolution,[],[f43,f39])).
% 2.97/0.81  fof(f43,plain,(
% 2.97/0.81    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 2.97/0.81    inference(cnf_transformation,[],[f23])).
% 2.97/0.81  fof(f23,plain,(
% 2.97/0.81    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.97/0.81    inference(ennf_transformation,[],[f17])).
% 2.97/0.81  fof(f17,axiom,(
% 2.97/0.81    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 2.97/0.81  fof(f373,plain,(
% 2.97/0.81    ( ! [X6,X7,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),X6) = k7_relat_1(k6_relat_1(X7),k4_xboole_0(X6,k4_xboole_0(X6,X5)))) )),
% 2.97/0.81    inference(forward_demodulation,[],[f361,f67])).
% 2.97/0.81  fof(f361,plain,(
% 2.97/0.81    ( ! [X6,X7,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),X6) = k7_relat_1(k6_relat_1(X7),k1_setfam_1(k1_enumset1(X6,X6,X5)))) )),
% 2.97/0.81    inference(superposition,[],[f144,f101])).
% 2.97/0.81  fof(f96,plain,(
% 2.97/0.81    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 2.97/0.81    inference(backward_demodulation,[],[f75,f94])).
% 2.97/0.81  fof(f75,plain,(
% 2.97/0.81    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.97/0.81    inference(backward_demodulation,[],[f64,f67])).
% 2.97/0.81  fof(f64,plain,(
% 2.97/0.81    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 2.97/0.81    inference(definition_unfolding,[],[f38,f63])).
% 2.97/0.81  fof(f38,plain,(
% 2.97/0.81    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.97/0.81    inference(cnf_transformation,[],[f35])).
% 2.97/0.81  fof(f35,plain,(
% 2.97/0.81    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.97/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f34])).
% 2.97/0.81  fof(f34,plain,(
% 2.97/0.81    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.97/0.81    introduced(choice_axiom,[])).
% 2.97/0.81  fof(f22,plain,(
% 2.97/0.81    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 2.97/0.81    inference(ennf_transformation,[],[f21])).
% 2.97/0.81  fof(f21,negated_conjecture,(
% 2.97/0.81    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.97/0.81    inference(negated_conjecture,[],[f20])).
% 2.97/0.81  fof(f20,conjecture,(
% 2.97/0.81    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.97/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 2.97/0.81  % SZS output end Proof for theBenchmark
% 2.97/0.81  % (3196)------------------------------
% 2.97/0.81  % (3196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.97/0.81  % (3196)Termination reason: Refutation
% 2.97/0.81  
% 2.97/0.81  % (3196)Memory used [KB]: 9850
% 2.97/0.81  % (3196)Time elapsed: 0.381 s
% 2.97/0.81  % (3196)------------------------------
% 2.97/0.81  % (3196)------------------------------
% 2.97/0.81  % (3295)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 2.97/0.82  % (3298)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 2.97/0.82  % (3298)Refutation not found, incomplete strategy% (3298)------------------------------
% 2.97/0.82  % (3298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.97/0.82  % (3298)Termination reason: Refutation not found, incomplete strategy
% 2.97/0.82  
% 2.97/0.82  % (3298)Memory used [KB]: 1663
% 2.97/0.82  % (3298)Time elapsed: 0.116 s
% 2.97/0.82  % (3298)------------------------------
% 2.97/0.82  % (3298)------------------------------
% 2.97/0.83  % (3167)Success in time 0.466 s
%------------------------------------------------------------------------------
