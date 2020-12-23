%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:32 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  113 (1385 expanded)
%              Number of leaves         :   21 ( 423 expanded)
%              Depth                    :   26
%              Number of atoms          :  167 (1938 expanded)
%              Number of equality atoms :  100 (1036 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1132,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1082])).

fof(f1082,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(superposition,[],[f243,f1004])).

fof(f1004,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(backward_demodulation,[],[f240,f914])).

fof(f914,plain,(
    ! [X4,X5] : k7_relat_1(k6_relat_1(X5),X4) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))),X5) ),
    inference(superposition,[],[f907,f522])).

fof(f522,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(superposition,[],[f512,f104])).

fof(f104,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f103,f79])).

fof(f79,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f51,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f103,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f102,f79])).

fof(f102,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f99,f40])).

fof(f40,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f99,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(resolution,[],[f98,f39])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f95,f40])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1))) ) ),
    inference(resolution,[],[f45,f39])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f512,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(superposition,[],[f232,f500])).

fof(f500,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(resolution,[],[f249,f85])).

fof(f85,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f84,f39])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f83,f39])).

fof(f83,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X2))
      | v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ) ),
    inference(superposition,[],[f55,f79])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f249,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))
      | k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ) ),
    inference(forward_demodulation,[],[f246,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f85,f51])).

fof(f246,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f241,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f241,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    inference(backward_demodulation,[],[f134,f238])).

fof(f238,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f234,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f234,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(resolution,[],[f233,f39])).

fof(f233,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(forward_demodulation,[],[f70,f69])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f134,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f68,f69])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f47,f66])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f232,plain,(
    ! [X6,X7,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) ),
    inference(forward_demodulation,[],[f231,f86])).

fof(f231,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6) ),
    inference(forward_demodulation,[],[f230,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] : k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(forward_demodulation,[],[f111,f79])).

fof(f111,plain,(
    ! [X2,X0,X1] : k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f108,f39])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ) ),
    inference(resolution,[],[f54,f39])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(f230,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5)) ),
    inference(forward_demodulation,[],[f101,f104])).

fof(f101,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)),k6_relat_1(X5)) ),
    inference(resolution,[],[f98,f85])).

fof(f907,plain,(
    ! [X35,X34] : k7_relat_1(k6_relat_1(X35),X34) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X34),X35))),X35) ),
    inference(forward_demodulation,[],[f906,f239])).

fof(f239,plain,(
    ! [X6,X5] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) = k7_relat_1(k6_relat_1(X5),k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) ),
    inference(backward_demodulation,[],[f143,f238])).

fof(f143,plain,(
    ! [X6,X5] : k6_relat_1(k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k7_relat_1(k6_relat_1(X5),k4_xboole_0(X5,k4_xboole_0(X5,X6))) ),
    inference(forward_demodulation,[],[f138,f40])).

fof(f138,plain,(
    ! [X6,X5] : k7_relat_1(k6_relat_1(X5),k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k4_relat_1(k6_relat_1(k4_xboole_0(X5,k4_xboole_0(X5,X6)))) ),
    inference(superposition,[],[f104,f135])).

fof(f135,plain,(
    ! [X0,X1] : k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))),X0) ),
    inference(resolution,[],[f134,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f92,f39])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f91,f79])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f53,f41])).

fof(f906,plain,(
    ! [X35,X34] : k7_relat_1(k6_relat_1(X35),X34) = k7_relat_1(k7_relat_1(k6_relat_1(X34),k1_relat_1(k7_relat_1(k6_relat_1(X34),X35))),X35) ),
    inference(forward_demodulation,[],[f905,f522])).

fof(f905,plain,(
    ! [X35,X34] : k7_relat_1(k6_relat_1(X35),X34) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X34),X35))),X34),X35) ),
    inference(forward_demodulation,[],[f890,f104])).

fof(f890,plain,(
    ! [X35,X34] : k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X34),X35))),X34),X35) = k4_relat_1(k7_relat_1(k6_relat_1(X34),X35)) ),
    inference(superposition,[],[f540,f167])).

fof(f167,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ),
    inference(superposition,[],[f87,f86])).

fof(f87,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))),k7_relat_1(k6_relat_1(X3),X4)) ),
    inference(resolution,[],[f85,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f540,plain,(
    ! [X26,X27,X25] : k7_relat_1(k7_relat_1(k6_relat_1(X27),X26),X25) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X26),X25),X27)) ),
    inference(superposition,[],[f232,f522])).

fof(f240,plain,(
    ! [X0,X1] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) ),
    inference(backward_demodulation,[],[f135,f238])).

fof(f243,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(backward_demodulation,[],[f133,f238])).

fof(f133,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f90,f69])).

fof(f90,plain,(
    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(forward_demodulation,[],[f67,f79])).

fof(f67,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f38,f66])).

fof(f38,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f36])).

fof(f36,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:11:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (825720832)
% 0.13/0.38  ipcrm: permission denied for id (825786379)
% 0.13/0.38  ipcrm: permission denied for id (825819148)
% 0.13/0.38  ipcrm: permission denied for id (825851918)
% 0.13/0.39  ipcrm: permission denied for id (825917462)
% 0.21/0.40  ipcrm: permission denied for id (825983006)
% 0.21/0.41  ipcrm: permission denied for id (826015776)
% 0.21/0.41  ipcrm: permission denied for id (826048548)
% 0.21/0.41  ipcrm: permission denied for id (826114086)
% 0.21/0.41  ipcrm: permission denied for id (826146855)
% 0.21/0.42  ipcrm: permission denied for id (826179626)
% 0.21/0.42  ipcrm: permission denied for id (826212396)
% 0.21/0.43  ipcrm: permission denied for id (826245170)
% 0.21/0.43  ipcrm: permission denied for id (826277942)
% 0.21/0.44  ipcrm: permission denied for id (826343482)
% 0.21/0.44  ipcrm: permission denied for id (826409022)
% 0.21/0.45  ipcrm: permission denied for id (826441792)
% 0.21/0.45  ipcrm: permission denied for id (826474564)
% 0.21/0.46  ipcrm: permission denied for id (826507336)
% 0.21/0.46  ipcrm: permission denied for id (826572877)
% 0.21/0.49  ipcrm: permission denied for id (826671201)
% 0.21/0.49  ipcrm: permission denied for id (826736741)
% 0.21/0.50  ipcrm: permission denied for id (826835050)
% 0.21/0.51  ipcrm: permission denied for id (826900594)
% 0.21/0.52  ipcrm: permission denied for id (826998909)
% 0.21/0.60  % (31141)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.60  % (31145)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.60  % (31136)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.96/0.64  % (31134)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.96/0.64  % (31135)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 1.11/0.65  % (31150)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.11/0.65  % (31142)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.11/0.65  % (31143)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.11/0.66  % (31137)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 1.32/0.67  % (31146)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.32/0.67  % (31140)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.32/0.67  % (31135)Refutation found. Thanks to Tanya!
% 1.32/0.67  % SZS status Theorem for theBenchmark
% 1.32/0.67  % SZS output start Proof for theBenchmark
% 1.32/0.67  fof(f1132,plain,(
% 1.32/0.67    $false),
% 1.32/0.67    inference(trivial_inequality_removal,[],[f1082])).
% 1.32/0.67  fof(f1082,plain,(
% 1.32/0.67    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.32/0.67    inference(superposition,[],[f243,f1004])).
% 1.32/0.67  fof(f1004,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 1.32/0.67    inference(backward_demodulation,[],[f240,f914])).
% 1.32/0.67  fof(f914,plain,(
% 1.32/0.67    ( ! [X4,X5] : (k7_relat_1(k6_relat_1(X5),X4) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))),X5)) )),
% 1.32/0.67    inference(superposition,[],[f907,f522])).
% 1.32/0.67  fof(f522,plain,(
% 1.32/0.67    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 1.32/0.67    inference(superposition,[],[f512,f104])).
% 1.32/0.67  fof(f104,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.32/0.67    inference(forward_demodulation,[],[f103,f79])).
% 1.32/0.67  fof(f79,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.32/0.67    inference(resolution,[],[f51,f39])).
% 1.32/0.67  fof(f39,plain,(
% 1.32/0.67    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.32/0.67    inference(cnf_transformation,[],[f11])).
% 1.32/0.67  fof(f11,axiom,(
% 1.32/0.67    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.32/0.67  fof(f51,plain,(
% 1.32/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.32/0.67    inference(cnf_transformation,[],[f29])).
% 1.32/0.67  fof(f29,plain,(
% 1.32/0.67    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.32/0.67    inference(ennf_transformation,[],[f21])).
% 1.32/0.67  fof(f21,axiom,(
% 1.32/0.67    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.32/0.67  fof(f103,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.32/0.67    inference(forward_demodulation,[],[f102,f79])).
% 1.32/0.67  fof(f102,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 1.32/0.67    inference(forward_demodulation,[],[f99,f40])).
% 1.32/0.67  fof(f40,plain,(
% 1.32/0.67    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 1.32/0.67    inference(cnf_transformation,[],[f16])).
% 1.32/0.67  fof(f16,axiom,(
% 1.32/0.67    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 1.32/0.67  fof(f99,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))) )),
% 1.32/0.67    inference(resolution,[],[f98,f39])).
% 1.32/0.67  fof(f98,plain,(
% 1.32/0.67    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) )),
% 1.32/0.67    inference(forward_demodulation,[],[f95,f40])).
% 1.32/0.67  fof(f95,plain,(
% 1.32/0.67    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1)))) )),
% 1.32/0.67    inference(resolution,[],[f45,f39])).
% 1.32/0.67  fof(f45,plain,(
% 1.32/0.67    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 1.32/0.67    inference(cnf_transformation,[],[f27])).
% 1.32/0.67  fof(f27,plain,(
% 1.32/0.67    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.32/0.67    inference(ennf_transformation,[],[f13])).
% 1.32/0.67  fof(f13,axiom,(
% 1.32/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 1.32/0.67  fof(f512,plain,(
% 1.32/0.67    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))) )),
% 1.32/0.67    inference(superposition,[],[f232,f500])).
% 1.32/0.67  fof(f500,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.32/0.67    inference(resolution,[],[f249,f85])).
% 1.32/0.67  fof(f85,plain,(
% 1.32/0.67    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.32/0.67    inference(resolution,[],[f84,f39])).
% 1.32/0.67  fof(f84,plain,(
% 1.32/0.67    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.32/0.67    inference(resolution,[],[f83,f39])).
% 1.32/0.67  fof(f83,plain,(
% 1.32/0.67    ( ! [X2,X1] : (~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X2)) | v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.32/0.67    inference(superposition,[],[f55,f79])).
% 1.32/0.67  fof(f55,plain,(
% 1.32/0.67    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.32/0.67    inference(cnf_transformation,[],[f35])).
% 1.32/0.67  fof(f35,plain,(
% 1.32/0.67    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.32/0.67    inference(flattening,[],[f34])).
% 1.32/0.67  fof(f34,plain,(
% 1.32/0.67    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.32/0.67    inference(ennf_transformation,[],[f10])).
% 1.32/0.67  fof(f10,axiom,(
% 1.32/0.67    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.32/0.67  fof(f249,plain,(
% 1.32/0.67    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) | k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.32/0.67    inference(forward_demodulation,[],[f246,f86])).
% 1.32/0.67  fof(f86,plain,(
% 1.32/0.67    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.32/0.67    inference(resolution,[],[f85,f51])).
% 1.32/0.67  fof(f246,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.32/0.67    inference(resolution,[],[f241,f53])).
% 1.32/0.67  fof(f53,plain,(
% 1.32/0.67    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 1.32/0.67    inference(cnf_transformation,[],[f32])).
% 1.32/0.67  fof(f32,plain,(
% 1.32/0.67    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.32/0.67    inference(flattening,[],[f31])).
% 1.32/0.67  fof(f31,plain,(
% 1.32/0.67    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.32/0.67    inference(ennf_transformation,[],[f17])).
% 1.32/0.67  fof(f17,axiom,(
% 1.32/0.67    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 1.32/0.67  fof(f241,plain,(
% 1.32/0.67    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) )),
% 1.32/0.67    inference(backward_demodulation,[],[f134,f238])).
% 1.32/0.67  fof(f238,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.32/0.67    inference(forward_demodulation,[],[f234,f41])).
% 1.32/0.67  fof(f41,plain,(
% 1.32/0.67    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.32/0.67    inference(cnf_transformation,[],[f15])).
% 1.32/0.67  fof(f15,axiom,(
% 1.32/0.67    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.32/0.67  fof(f234,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) )),
% 1.32/0.67    inference(resolution,[],[f233,f39])).
% 1.32/0.67  fof(f233,plain,(
% 1.32/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) )),
% 1.32/0.67    inference(forward_demodulation,[],[f70,f69])).
% 1.32/0.67  fof(f69,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.32/0.67    inference(definition_unfolding,[],[f50,f66])).
% 1.32/0.67  fof(f66,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.32/0.67    inference(definition_unfolding,[],[f48,f65])).
% 1.32/0.67  fof(f65,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.32/0.67    inference(definition_unfolding,[],[f49,f64])).
% 1.32/0.67  fof(f64,plain,(
% 1.32/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.32/0.67    inference(definition_unfolding,[],[f56,f63])).
% 1.32/0.67  fof(f63,plain,(
% 1.32/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.32/0.67    inference(definition_unfolding,[],[f57,f62])).
% 1.32/0.67  fof(f62,plain,(
% 1.32/0.67    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.32/0.67    inference(definition_unfolding,[],[f58,f61])).
% 1.32/0.67  fof(f61,plain,(
% 1.32/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.32/0.67    inference(definition_unfolding,[],[f59,f60])).
% 1.32/0.67  fof(f60,plain,(
% 1.32/0.67    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.32/0.67    inference(cnf_transformation,[],[f8])).
% 1.32/0.67  fof(f8,axiom,(
% 1.32/0.67    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.32/0.67  fof(f59,plain,(
% 1.32/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.32/0.67    inference(cnf_transformation,[],[f7])).
% 1.32/0.67  fof(f7,axiom,(
% 1.32/0.67    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.32/0.67  fof(f58,plain,(
% 1.32/0.67    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.32/0.67    inference(cnf_transformation,[],[f6])).
% 1.32/0.67  fof(f6,axiom,(
% 1.32/0.67    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.32/0.67  fof(f57,plain,(
% 1.32/0.67    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.32/0.67    inference(cnf_transformation,[],[f5])).
% 1.32/0.67  fof(f5,axiom,(
% 1.32/0.67    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.32/0.67  fof(f56,plain,(
% 1.32/0.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.67    inference(cnf_transformation,[],[f4])).
% 1.32/0.67  fof(f4,axiom,(
% 1.32/0.67    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.67  fof(f49,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.32/0.67    inference(cnf_transformation,[],[f3])).
% 1.32/0.67  fof(f3,axiom,(
% 1.32/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.67  fof(f48,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.32/0.67    inference(cnf_transformation,[],[f9])).
% 1.32/0.67  fof(f9,axiom,(
% 1.32/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.32/0.67  fof(f50,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.32/0.67    inference(cnf_transformation,[],[f2])).
% 1.32/0.67  fof(f2,axiom,(
% 1.32/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.32/0.67  fof(f70,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.32/0.67    inference(definition_unfolding,[],[f52,f66])).
% 1.32/0.67  fof(f52,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.32/0.67    inference(cnf_transformation,[],[f30])).
% 1.32/0.67  fof(f30,plain,(
% 1.32/0.67    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.32/0.67    inference(ennf_transformation,[],[f20])).
% 1.32/0.67  fof(f20,axiom,(
% 1.32/0.67    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.32/0.67  fof(f134,plain,(
% 1.32/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.32/0.67    inference(backward_demodulation,[],[f68,f69])).
% 1.32/0.67  fof(f68,plain,(
% 1.32/0.67    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 1.32/0.67    inference(definition_unfolding,[],[f47,f66])).
% 1.32/0.67  fof(f47,plain,(
% 1.32/0.67    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.32/0.67    inference(cnf_transformation,[],[f1])).
% 1.32/0.67  fof(f1,axiom,(
% 1.32/0.67    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.32/0.67  fof(f232,plain,(
% 1.32/0.67    ( ! [X6,X7,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))) )),
% 1.32/0.67    inference(forward_demodulation,[],[f231,f86])).
% 1.32/0.67  fof(f231,plain,(
% 1.32/0.67    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)) )),
% 1.32/0.67    inference(forward_demodulation,[],[f230,f114])).
% 1.32/0.67  fof(f114,plain,(
% 1.32/0.67    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) )),
% 1.32/0.67    inference(forward_demodulation,[],[f111,f79])).
% 1.32/0.67  fof(f111,plain,(
% 1.32/0.67    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))) )),
% 1.32/0.67    inference(resolution,[],[f108,f39])).
% 1.32/0.67  fof(f108,plain,(
% 1.32/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)) )),
% 1.32/0.67    inference(resolution,[],[f54,f39])).
% 1.32/0.67  fof(f54,plain,(
% 1.32/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)) )),
% 1.32/0.67    inference(cnf_transformation,[],[f33])).
% 1.32/0.67  fof(f33,plain,(
% 1.32/0.67    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.32/0.67    inference(ennf_transformation,[],[f12])).
% 1.32/0.67  fof(f12,axiom,(
% 1.32/0.67    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).
% 1.32/0.67  fof(f230,plain,(
% 1.32/0.67    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5))) )),
% 1.32/0.67    inference(forward_demodulation,[],[f101,f104])).
% 1.32/0.67  fof(f101,plain,(
% 1.32/0.67    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)),k6_relat_1(X5))) )),
% 1.32/0.67    inference(resolution,[],[f98,f85])).
% 1.32/0.67  fof(f907,plain,(
% 1.32/0.67    ( ! [X35,X34] : (k7_relat_1(k6_relat_1(X35),X34) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X34),X35))),X35)) )),
% 1.32/0.67    inference(forward_demodulation,[],[f906,f239])).
% 1.32/0.67  fof(f239,plain,(
% 1.32/0.67    ( ! [X6,X5] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) = k7_relat_1(k6_relat_1(X5),k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)))) )),
% 1.32/0.67    inference(backward_demodulation,[],[f143,f238])).
% 1.32/0.67  fof(f143,plain,(
% 1.32/0.67    ( ! [X6,X5] : (k6_relat_1(k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k7_relat_1(k6_relat_1(X5),k4_xboole_0(X5,k4_xboole_0(X5,X6)))) )),
% 1.32/0.67    inference(forward_demodulation,[],[f138,f40])).
% 1.32/0.67  fof(f138,plain,(
% 1.32/0.67    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X5),k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k4_relat_1(k6_relat_1(k4_xboole_0(X5,k4_xboole_0(X5,X6))))) )),
% 1.32/0.67    inference(superposition,[],[f104,f135])).
% 1.32/0.67  fof(f135,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))),X0)) )),
% 1.32/0.67    inference(resolution,[],[f134,f93])).
% 1.32/0.67  fof(f93,plain,(
% 1.32/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.32/0.67    inference(resolution,[],[f92,f39])).
% 1.32/0.67  fof(f92,plain,(
% 1.32/0.67    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.32/0.67    inference(forward_demodulation,[],[f91,f79])).
% 1.32/0.67  fof(f91,plain,(
% 1.32/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.32/0.67    inference(superposition,[],[f53,f41])).
% 1.32/0.67  fof(f906,plain,(
% 1.32/0.67    ( ! [X35,X34] : (k7_relat_1(k6_relat_1(X35),X34) = k7_relat_1(k7_relat_1(k6_relat_1(X34),k1_relat_1(k7_relat_1(k6_relat_1(X34),X35))),X35)) )),
% 1.32/0.67    inference(forward_demodulation,[],[f905,f522])).
% 1.32/0.67  fof(f905,plain,(
% 1.32/0.67    ( ! [X35,X34] : (k7_relat_1(k6_relat_1(X35),X34) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X34),X35))),X34),X35)) )),
% 1.32/0.67    inference(forward_demodulation,[],[f890,f104])).
% 1.32/0.67  fof(f890,plain,(
% 1.32/0.67    ( ! [X35,X34] : (k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X34),X35))),X34),X35) = k4_relat_1(k7_relat_1(k6_relat_1(X34),X35))) )),
% 1.32/0.67    inference(superposition,[],[f540,f167])).
% 1.32/0.67  fof(f167,plain,(
% 1.32/0.67    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) )),
% 1.32/0.67    inference(superposition,[],[f87,f86])).
% 1.32/0.67  fof(f87,plain,(
% 1.32/0.67    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))),k7_relat_1(k6_relat_1(X3),X4))) )),
% 1.32/0.67    inference(resolution,[],[f85,f44])).
% 1.32/0.67  fof(f44,plain,(
% 1.32/0.67    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 1.32/0.67    inference(cnf_transformation,[],[f26])).
% 1.32/0.67  fof(f26,plain,(
% 1.32/0.67    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.32/0.67    inference(ennf_transformation,[],[f18])).
% 1.32/0.67  fof(f18,axiom,(
% 1.32/0.67    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 1.32/0.67  fof(f540,plain,(
% 1.32/0.67    ( ! [X26,X27,X25] : (k7_relat_1(k7_relat_1(k6_relat_1(X27),X26),X25) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X26),X25),X27))) )),
% 1.32/0.67    inference(superposition,[],[f232,f522])).
% 1.32/0.67  fof(f240,plain,(
% 1.32/0.67    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0)) )),
% 1.32/0.67    inference(backward_demodulation,[],[f135,f238])).
% 1.32/0.67  fof(f243,plain,(
% 1.32/0.67    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 1.32/0.67    inference(backward_demodulation,[],[f133,f238])).
% 1.32/0.67  fof(f133,plain,(
% 1.32/0.67    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.32/0.67    inference(backward_demodulation,[],[f90,f69])).
% 1.32/0.67  fof(f90,plain,(
% 1.32/0.67    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.32/0.67    inference(forward_demodulation,[],[f67,f79])).
% 1.32/0.67  fof(f67,plain,(
% 1.32/0.67    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 1.32/0.67    inference(definition_unfolding,[],[f38,f66])).
% 1.32/0.67  fof(f38,plain,(
% 1.32/0.67    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.32/0.67    inference(cnf_transformation,[],[f37])).
% 1.32/0.67  fof(f37,plain,(
% 1.32/0.67    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.32/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f36])).
% 1.32/0.67  fof(f36,plain,(
% 1.32/0.67    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.32/0.67    introduced(choice_axiom,[])).
% 1.32/0.67  fof(f24,plain,(
% 1.32/0.67    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.32/0.67    inference(ennf_transformation,[],[f23])).
% 1.32/0.67  fof(f23,negated_conjecture,(
% 1.32/0.67    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.32/0.67    inference(negated_conjecture,[],[f22])).
% 1.32/0.67  fof(f22,conjecture,(
% 1.32/0.67    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.32/0.67  % SZS output end Proof for theBenchmark
% 1.32/0.67  % (31135)------------------------------
% 1.32/0.67  % (31135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.67  % (31135)Termination reason: Refutation
% 1.32/0.67  
% 1.32/0.67  % (31135)Memory used [KB]: 6652
% 1.32/0.67  % (31135)Time elapsed: 0.076 s
% 1.32/0.67  % (31135)------------------------------
% 1.32/0.67  % (31135)------------------------------
% 1.32/0.67  % (31133)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.32/0.68  % (31138)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 1.32/0.68  % (31144)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.32/0.68  % (31144)Refutation not found, incomplete strategy% (31144)------------------------------
% 1.32/0.68  % (31144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.68  % (31148)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.32/0.68  % (31147)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.32/0.69  % (30978)Success in time 0.32 s
%------------------------------------------------------------------------------
