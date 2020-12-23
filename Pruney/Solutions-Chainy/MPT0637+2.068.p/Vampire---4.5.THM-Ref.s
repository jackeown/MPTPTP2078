%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:32 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  176 (4139 expanded)
%              Number of leaves         :   24 (1245 expanded)
%              Depth                    :   27
%              Number of atoms          :  269 (6140 expanded)
%              Number of equality atoms :  145 (2871 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1749,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1708,f1546])).

fof(f1546,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(superposition,[],[f1489,f184])).

fof(f184,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f183,f83])).

fof(f83,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f183,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f182,f83])).

fof(f182,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f179,f43])).

fof(f43,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f179,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(resolution,[],[f178,f42])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f175,f43])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1))) ) ),
    inference(resolution,[],[f49,f42])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f1489,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f1428,f227])).

fof(f227,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(superposition,[],[f91,f211])).

fof(f211,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(subsumption_resolution,[],[f205,f90])).

fof(f90,plain,(
    ! [X2,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(subsumption_resolution,[],[f89,f42])).

fof(f89,plain,(
    ! [X2,X1] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f88,f42])).

fof(f88,plain,(
    ! [X2,X1] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f59,f83])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f205,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f200,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f200,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    inference(backward_demodulation,[],[f76,f197])).

fof(f197,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f194,f44])).

fof(f44,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f194,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(resolution,[],[f77,f42])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(forward_demodulation,[],[f74,f73])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f72,f73])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f91,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(resolution,[],[f90,f55])).

fof(f1428,plain,(
    ! [X6,X4,X5] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X4) ),
    inference(forward_demodulation,[],[f1427,f91])).

fof(f1427,plain,(
    ! [X6,X4,X5] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X6)) = k5_relat_1(k6_relat_1(X4),k7_relat_1(k6_relat_1(X6),X5)) ),
    inference(forward_demodulation,[],[f1426,f83])).

fof(f1426,plain,(
    ! [X6,X4,X5] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X6)) = k5_relat_1(k6_relat_1(X4),k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) ),
    inference(forward_demodulation,[],[f1425,f187])).

fof(f187,plain,(
    ! [X6,X7,X5] : k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) ),
    inference(forward_demodulation,[],[f186,f91])).

fof(f186,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5)) ),
    inference(forward_demodulation,[],[f181,f184])).

fof(f181,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)),k6_relat_1(X5)) ),
    inference(resolution,[],[f178,f90])).

fof(f1425,plain,(
    ! [X6,X4,X5] : k5_relat_1(k6_relat_1(X4),k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k7_relat_1(k6_relat_1(X5),X4),k6_relat_1(X6)) ),
    inference(forward_demodulation,[],[f1421,f83])).

fof(f1421,plain,(
    ! [X6,X4,X5] : k5_relat_1(k6_relat_1(X4),k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k5_relat_1(k6_relat_1(X4),k6_relat_1(X5)),k6_relat_1(X6)) ),
    inference(resolution,[],[f1391,f42])).

fof(f1391,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X4)
      | k5_relat_1(k5_relat_1(k6_relat_1(X5),X4),k6_relat_1(X6)) = k5_relat_1(k6_relat_1(X5),k5_relat_1(X4,k6_relat_1(X6))) ) ),
    inference(resolution,[],[f1381,f42])).

fof(f1381,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(X4,X5),k6_relat_1(X6)) = k5_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6))) ) ),
    inference(resolution,[],[f50,f42])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f1708,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(superposition,[],[f1640,f1521])).

fof(f1521,plain,(
    ! [X2,X3] : k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k6_relat_1(X2),X3) ),
    inference(backward_demodulation,[],[f619,f1520])).

fof(f1520,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X1),X0)),X0) ),
    inference(forward_demodulation,[],[f1491,f144])).

fof(f144,plain,(
    ! [X4,X5] : k6_relat_1(k9_relat_1(k6_relat_1(X4),X5)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X4),X5)),X4) ),
    inference(backward_demodulation,[],[f120,f140])).

fof(f140,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f137,f83])).

fof(f137,plain,(
    ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f136,f42])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1) ) ),
    inference(forward_demodulation,[],[f133,f45])).

fof(f45,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,k2_relat_1(k6_relat_1(X1))) ) ),
    inference(resolution,[],[f48,f42])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f120,plain,(
    ! [X4,X5] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X4),X5))),X4) ),
    inference(resolution,[],[f113,f102])).

fof(f102,plain,(
    ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2) ),
    inference(forward_demodulation,[],[f101,f45])).

fof(f101,plain,(
    ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2))) ),
    inference(subsumption_resolution,[],[f100,f42])).

fof(f100,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f95,f42])).

fof(f95,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f47,f83])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f112,f83])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f111,f42])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f57,f44])).

fof(f1491,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X1),X0)),X1),X0) ),
    inference(superposition,[],[f1428,f539])).

fof(f539,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),k9_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[],[f187,f146])).

fof(f146,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(k9_relat_1(k6_relat_1(X3),X4))) ),
    inference(backward_demodulation,[],[f92,f140])).

fof(f92,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)))) ),
    inference(resolution,[],[f90,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f619,plain,(
    ! [X2,X3] : k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3) ),
    inference(resolution,[],[f617,f113])).

fof(f617,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X0) ),
    inference(forward_demodulation,[],[f616,f140])).

fof(f616,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X0) ),
    inference(forward_demodulation,[],[f601,f184])).

fof(f601,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) ),
    inference(superposition,[],[f557,f227])).

fof(f557,plain,(
    ! [X4,X2,X3] : r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X4))),X4) ),
    inference(subsumption_resolution,[],[f541,f90])).

fof(f541,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X4))),X4)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) ) ),
    inference(superposition,[],[f103,f187])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f96,f42])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))),X0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f47,f45])).

fof(f1640,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k9_relat_1(k6_relat_1(sK1),sK0)) ),
    inference(backward_demodulation,[],[f203,f1621])).

fof(f1621,plain,(
    ! [X24,X25] : k1_relat_1(k7_relat_1(k6_relat_1(X24),X25)) = k9_relat_1(k6_relat_1(X25),X24) ),
    inference(forward_demodulation,[],[f1614,f1531])).

fof(f1531,plain,(
    ! [X37,X36] : k9_relat_1(k6_relat_1(X37),X36) = k9_relat_1(k7_relat_1(k6_relat_1(X37),X36),X36) ),
    inference(backward_demodulation,[],[f664,f1521])).

fof(f664,plain,(
    ! [X37,X36] : k9_relat_1(k6_relat_1(X37),X36) = k9_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X37),X36)),X36) ),
    inference(forward_demodulation,[],[f649,f654])).

fof(f654,plain,(
    ! [X6,X7] : k9_relat_1(k6_relat_1(X7),X6) = k9_relat_1(k6_relat_1(X6),k9_relat_1(k6_relat_1(X7),X6)) ),
    inference(forward_demodulation,[],[f636,f45])).

fof(f636,plain,(
    ! [X6,X7] : k9_relat_1(k6_relat_1(X6),k9_relat_1(k6_relat_1(X7),X6)) = k2_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X7),X6))) ),
    inference(superposition,[],[f140,f618])).

fof(f618,plain,(
    ! [X0,X1] : k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f617,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f126,f83])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f123,f45])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f58,f42])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f649,plain,(
    ! [X37,X36] : k9_relat_1(k6_relat_1(X36),k9_relat_1(k6_relat_1(X37),X36)) = k9_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X37),X36)),X36) ),
    inference(superposition,[],[f277,f618])).

fof(f277,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(forward_demodulation,[],[f275,f140])).

fof(f275,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(superposition,[],[f147,f227])).

fof(f147,plain,(
    ! [X6,X7,X5] : k9_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) ),
    inference(forward_demodulation,[],[f139,f91])).

fof(f139,plain,(
    ! [X6,X7,X5] : k2_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k9_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5) ),
    inference(resolution,[],[f136,f90])).

fof(f1614,plain,(
    ! [X24,X25] : k1_relat_1(k7_relat_1(k6_relat_1(X24),X25)) = k9_relat_1(k7_relat_1(k6_relat_1(X25),X24),X24) ),
    inference(backward_demodulation,[],[f323,f1609])).

fof(f1609,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(backward_demodulation,[],[f199,f1608])).

fof(f1608,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(backward_demodulation,[],[f1549,f1562])).

fof(f1562,plain,(
    ! [X15,X16] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X16),X15))) = k7_relat_1(k6_relat_1(X15),k1_relat_1(k7_relat_1(k6_relat_1(X16),X15))) ),
    inference(superposition,[],[f198,f1546])).

fof(f198,plain,(
    ! [X0,X1] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(backward_demodulation,[],[f128,f197])).

fof(f128,plain,(
    ! [X0,X1] : k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(resolution,[],[f127,f76])).

fof(f1549,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2) ),
    inference(backward_demodulation,[],[f1519,f1546])).

fof(f1519,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3),X2) ),
    inference(forward_demodulation,[],[f1490,f184])).

fof(f1490,plain,(
    ! [X2,X3] : k4_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3),X2) ),
    inference(superposition,[],[f1428,f1007])).

fof(f1007,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ),
    inference(superposition,[],[f116,f91])).

fof(f116,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))),k7_relat_1(k6_relat_1(X3),X4)) ),
    inference(resolution,[],[f110,f90])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(resolution,[],[f57,f99])).

fof(f99,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f98,f45])).

fof(f98,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0))) ),
    inference(subsumption_resolution,[],[f97,f42])).

fof(f97,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f47,f80])).

fof(f80,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f78,f45])).

fof(f78,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) ),
    inference(resolution,[],[f46,f42])).

fof(f199,plain,(
    ! [X0,X1] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) ),
    inference(backward_demodulation,[],[f118,f197])).

fof(f118,plain,(
    ! [X0,X1] : k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))),X0) ),
    inference(resolution,[],[f113,f76])).

fof(f323,plain,(
    ! [X24,X25] : k1_relat_1(k7_relat_1(k6_relat_1(X24),X25)) = k9_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X24),X25))),X24) ),
    inference(forward_demodulation,[],[f314,f319])).

fof(f319,plain,(
    ! [X6,X5] : k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)) = k9_relat_1(k6_relat_1(X5),k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) ),
    inference(forward_demodulation,[],[f306,f45])).

fof(f306,plain,(
    ! [X6,X5] : k9_relat_1(k6_relat_1(X5),k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) = k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)))) ),
    inference(superposition,[],[f140,f198])).

fof(f314,plain,(
    ! [X24,X25] : k9_relat_1(k6_relat_1(X24),k1_relat_1(k7_relat_1(k6_relat_1(X24),X25))) = k9_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X24),X25))),X24) ),
    inference(superposition,[],[f277,f198])).

fof(f203,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(backward_demodulation,[],[f85,f197])).

fof(f85,plain,(
    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f75,f83])).

fof(f75,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f71,f73])).

fof(f71,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f41,f70])).

fof(f41,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f39])).

fof(f39,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:18:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (21996)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (21991)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (22000)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (21995)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (22002)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (21994)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (21988)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (21999)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (21990)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.52  % (21997)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.20/0.52  % (21998)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.20/0.53  % (21986)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.20/0.53  % (22003)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.20/0.53  % (21997)Refutation not found, incomplete strategy% (21997)------------------------------
% 1.20/0.53  % (21997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (21997)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (21997)Memory used [KB]: 10618
% 1.20/0.53  % (21997)Time elapsed: 0.098 s
% 1.20/0.53  % (21997)------------------------------
% 1.20/0.53  % (21997)------------------------------
% 1.20/0.53  % (21989)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 1.20/0.53  % (21992)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.34/0.54  % (21985)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.34/0.54  % (22001)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.34/0.54  % (21987)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 1.34/0.56  % (22000)Refutation found. Thanks to Tanya!
% 1.34/0.56  % SZS status Theorem for theBenchmark
% 1.34/0.56  % SZS output start Proof for theBenchmark
% 1.34/0.56  fof(f1749,plain,(
% 1.34/0.56    $false),
% 1.34/0.56    inference(subsumption_resolution,[],[f1708,f1546])).
% 1.34/0.56  fof(f1546,plain,(
% 1.34/0.56    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 1.34/0.56    inference(superposition,[],[f1489,f184])).
% 1.34/0.56  fof(f184,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f183,f83])).
% 1.34/0.56  fof(f83,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 1.34/0.56    inference(resolution,[],[f55,f42])).
% 1.34/0.56  fof(f42,plain,(
% 1.34/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.34/0.56    inference(cnf_transformation,[],[f11])).
% 1.34/0.56  fof(f11,axiom,(
% 1.34/0.56    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.34/0.56  fof(f55,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f31])).
% 1.34/0.56  fof(f31,plain,(
% 1.34/0.56    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.34/0.56    inference(ennf_transformation,[],[f22])).
% 1.34/0.56  fof(f22,axiom,(
% 1.34/0.56    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.34/0.56  fof(f183,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f182,f83])).
% 1.34/0.56  fof(f182,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f179,f43])).
% 1.34/0.56  fof(f43,plain,(
% 1.34/0.56    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 1.34/0.56    inference(cnf_transformation,[],[f17])).
% 1.34/0.56  fof(f17,axiom,(
% 1.34/0.56    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 1.34/0.56  fof(f179,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))) )),
% 1.34/0.56    inference(resolution,[],[f178,f42])).
% 1.34/0.56  fof(f178,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f175,f43])).
% 1.34/0.56  fof(f175,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1)))) )),
% 1.34/0.56    inference(resolution,[],[f49,f42])).
% 1.34/0.56  fof(f49,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 1.34/0.56    inference(cnf_transformation,[],[f29])).
% 1.34/0.56  fof(f29,plain,(
% 1.34/0.56    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.34/0.56    inference(ennf_transformation,[],[f14])).
% 1.34/0.56  fof(f14,axiom,(
% 1.34/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.34/0.56  fof(f1489,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.34/0.56    inference(superposition,[],[f1428,f227])).
% 1.34/0.56  fof(f227,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.34/0.56    inference(superposition,[],[f91,f211])).
% 1.34/0.56  fof(f211,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.34/0.56    inference(subsumption_resolution,[],[f205,f90])).
% 1.34/0.56  fof(f90,plain,(
% 1.34/0.56    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.34/0.56    inference(subsumption_resolution,[],[f89,f42])).
% 1.34/0.56  fof(f89,plain,(
% 1.34/0.56    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.34/0.56    inference(subsumption_resolution,[],[f88,f42])).
% 1.34/0.56  fof(f88,plain,(
% 1.34/0.56    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.34/0.56    inference(superposition,[],[f59,f83])).
% 1.34/0.56  fof(f59,plain,(
% 1.34/0.56    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f38])).
% 1.34/0.56  fof(f38,plain,(
% 1.34/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.34/0.56    inference(flattening,[],[f37])).
% 1.34/0.56  fof(f37,plain,(
% 1.34/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.34/0.56    inference(ennf_transformation,[],[f10])).
% 1.34/0.56  fof(f10,axiom,(
% 1.34/0.56    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.34/0.56  fof(f205,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.34/0.56    inference(resolution,[],[f200,f57])).
% 1.34/0.56  fof(f57,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f34])).
% 1.34/0.56  fof(f34,plain,(
% 1.34/0.56    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.34/0.56    inference(flattening,[],[f33])).
% 1.34/0.56  fof(f33,plain,(
% 1.34/0.56    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.34/0.56    inference(ennf_transformation,[],[f18])).
% 1.34/0.56  fof(f18,axiom,(
% 1.34/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 1.34/0.56  fof(f200,plain,(
% 1.34/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) )),
% 1.34/0.56    inference(backward_demodulation,[],[f76,f197])).
% 1.34/0.56  fof(f197,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f194,f44])).
% 1.34/0.56  fof(f44,plain,(
% 1.34/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.34/0.56    inference(cnf_transformation,[],[f16])).
% 1.34/0.56  fof(f16,axiom,(
% 1.34/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.34/0.56  fof(f194,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) )),
% 1.34/0.56    inference(resolution,[],[f77,f42])).
% 1.34/0.56  fof(f77,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f74,f73])).
% 1.34/0.56  fof(f73,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.34/0.56    inference(definition_unfolding,[],[f54,f70])).
% 1.34/0.56  fof(f70,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.34/0.56    inference(definition_unfolding,[],[f52,f69])).
% 1.34/0.56  fof(f69,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.34/0.56    inference(definition_unfolding,[],[f53,f68])).
% 1.34/0.56  fof(f68,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.34/0.56    inference(definition_unfolding,[],[f60,f67])).
% 1.34/0.56  fof(f67,plain,(
% 1.34/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.34/0.56    inference(definition_unfolding,[],[f61,f66])).
% 1.34/0.56  fof(f66,plain,(
% 1.34/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.34/0.56    inference(definition_unfolding,[],[f62,f65])).
% 1.34/0.56  fof(f65,plain,(
% 1.34/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.34/0.56    inference(definition_unfolding,[],[f63,f64])).
% 1.34/0.56  fof(f64,plain,(
% 1.34/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f8])).
% 1.34/0.56  fof(f8,axiom,(
% 1.34/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.34/0.56  fof(f63,plain,(
% 1.34/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f7])).
% 1.34/0.56  fof(f7,axiom,(
% 1.34/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.34/0.56  fof(f62,plain,(
% 1.34/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f6])).
% 1.34/0.56  fof(f6,axiom,(
% 1.34/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.34/0.56  fof(f61,plain,(
% 1.34/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f5])).
% 1.34/0.56  fof(f5,axiom,(
% 1.34/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.34/0.56  fof(f60,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f4])).
% 1.34/0.56  fof(f4,axiom,(
% 1.34/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.34/0.56  fof(f53,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f3])).
% 1.34/0.56  fof(f3,axiom,(
% 1.34/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.56  fof(f52,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.34/0.56    inference(cnf_transformation,[],[f9])).
% 1.34/0.56  fof(f9,axiom,(
% 1.34/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.34/0.56  fof(f54,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.34/0.56    inference(cnf_transformation,[],[f2])).
% 1.34/0.56  fof(f2,axiom,(
% 1.34/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.34/0.56  fof(f74,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.34/0.56    inference(definition_unfolding,[],[f56,f70])).
% 1.34/0.56  fof(f56,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f32])).
% 1.34/0.56  fof(f32,plain,(
% 1.34/0.56    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.34/0.56    inference(ennf_transformation,[],[f21])).
% 1.34/0.56  fof(f21,axiom,(
% 1.34/0.56    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.34/0.56  fof(f76,plain,(
% 1.34/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.34/0.56    inference(backward_demodulation,[],[f72,f73])).
% 1.34/0.56  fof(f72,plain,(
% 1.34/0.56    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 1.34/0.56    inference(definition_unfolding,[],[f51,f70])).
% 1.34/0.56  fof(f51,plain,(
% 1.34/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f1])).
% 1.34/0.56  fof(f1,axiom,(
% 1.34/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.34/0.56  fof(f91,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)) )),
% 1.34/0.56    inference(resolution,[],[f90,f55])).
% 1.34/0.56  fof(f1428,plain,(
% 1.34/0.56    ( ! [X6,X4,X5] : (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X4)) )),
% 1.34/0.56    inference(forward_demodulation,[],[f1427,f91])).
% 1.34/0.56  fof(f1427,plain,(
% 1.34/0.56    ( ! [X6,X4,X5] : (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X6)) = k5_relat_1(k6_relat_1(X4),k7_relat_1(k6_relat_1(X6),X5))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f1426,f83])).
% 1.34/0.56  fof(f1426,plain,(
% 1.34/0.56    ( ! [X6,X4,X5] : (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X6)) = k5_relat_1(k6_relat_1(X4),k5_relat_1(k6_relat_1(X5),k6_relat_1(X6)))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f1425,f187])).
% 1.34/0.56  fof(f187,plain,(
% 1.34/0.56    ( ! [X6,X7,X5] : (k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f186,f91])).
% 1.34/0.56  fof(f186,plain,(
% 1.34/0.56    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f181,f184])).
% 1.34/0.56  fof(f181,plain,(
% 1.34/0.56    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)),k6_relat_1(X5))) )),
% 1.34/0.56    inference(resolution,[],[f178,f90])).
% 1.34/0.56  fof(f1425,plain,(
% 1.34/0.56    ( ! [X6,X4,X5] : (k5_relat_1(k6_relat_1(X4),k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k7_relat_1(k6_relat_1(X5),X4),k6_relat_1(X6))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f1421,f83])).
% 1.34/0.56  fof(f1421,plain,(
% 1.34/0.56    ( ! [X6,X4,X5] : (k5_relat_1(k6_relat_1(X4),k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k5_relat_1(k6_relat_1(X4),k6_relat_1(X5)),k6_relat_1(X6))) )),
% 1.34/0.56    inference(resolution,[],[f1391,f42])).
% 1.34/0.56  fof(f1391,plain,(
% 1.34/0.56    ( ! [X6,X4,X5] : (~v1_relat_1(X4) | k5_relat_1(k5_relat_1(k6_relat_1(X5),X4),k6_relat_1(X6)) = k5_relat_1(k6_relat_1(X5),k5_relat_1(X4,k6_relat_1(X6)))) )),
% 1.34/0.56    inference(resolution,[],[f1381,f42])).
% 1.34/0.56  fof(f1381,plain,(
% 1.34/0.56    ( ! [X6,X4,X5] : (~v1_relat_1(X4) | ~v1_relat_1(X5) | k5_relat_1(k5_relat_1(X4,X5),k6_relat_1(X6)) = k5_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6)))) )),
% 1.34/0.56    inference(resolution,[],[f50,f42])).
% 1.34/0.56  fof(f50,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f30])).
% 1.34/0.56  fof(f30,plain,(
% 1.34/0.56    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.34/0.56    inference(ennf_transformation,[],[f15])).
% 1.34/0.56  fof(f15,axiom,(
% 1.34/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 1.34/0.56  fof(f1708,plain,(
% 1.34/0.56    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0)),
% 1.34/0.56    inference(superposition,[],[f1640,f1521])).
% 1.34/0.56  fof(f1521,plain,(
% 1.34/0.56    ( ! [X2,X3] : (k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k6_relat_1(X2),X3)) )),
% 1.34/0.56    inference(backward_demodulation,[],[f619,f1520])).
% 1.34/0.56  fof(f1520,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X1),X0)),X0)) )),
% 1.34/0.56    inference(forward_demodulation,[],[f1491,f144])).
% 1.34/0.56  fof(f144,plain,(
% 1.34/0.56    ( ! [X4,X5] : (k6_relat_1(k9_relat_1(k6_relat_1(X4),X5)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X4),X5)),X4)) )),
% 1.34/0.56    inference(backward_demodulation,[],[f120,f140])).
% 1.34/0.56  fof(f140,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f137,f83])).
% 1.34/0.56  fof(f137,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)) )),
% 1.34/0.56    inference(resolution,[],[f136,f42])).
% 1.34/0.56  fof(f136,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1)) )),
% 1.34/0.56    inference(forward_demodulation,[],[f133,f45])).
% 1.34/0.56  fof(f45,plain,(
% 1.34/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.34/0.56    inference(cnf_transformation,[],[f16])).
% 1.34/0.56  fof(f133,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,k2_relat_1(k6_relat_1(X1)))) )),
% 1.34/0.56    inference(resolution,[],[f48,f42])).
% 1.34/0.56  fof(f48,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 1.34/0.56    inference(cnf_transformation,[],[f28])).
% 1.34/0.56  fof(f28,plain,(
% 1.34/0.56    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.34/0.56    inference(ennf_transformation,[],[f12])).
% 1.34/0.56  fof(f12,axiom,(
% 1.34/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 1.34/0.56  fof(f120,plain,(
% 1.34/0.56    ( ! [X4,X5] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X4),X5))),X4)) )),
% 1.34/0.56    inference(resolution,[],[f113,f102])).
% 1.34/0.56  fof(f102,plain,(
% 1.34/0.56    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2)) )),
% 1.34/0.56    inference(forward_demodulation,[],[f101,f45])).
% 1.34/0.56  fof(f101,plain,(
% 1.34/0.56    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))) )),
% 1.34/0.56    inference(subsumption_resolution,[],[f100,f42])).
% 1.34/0.56  fof(f100,plain,(
% 1.34/0.56    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.34/0.56    inference(subsumption_resolution,[],[f95,f42])).
% 1.34/0.56  fof(f95,plain,(
% 1.34/0.56    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.34/0.56    inference(superposition,[],[f47,f83])).
% 1.34/0.56  fof(f47,plain,(
% 1.34/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f27])).
% 1.34/0.56  fof(f27,plain,(
% 1.34/0.56    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.34/0.56    inference(ennf_transformation,[],[f13])).
% 1.34/0.56  fof(f13,axiom,(
% 1.34/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.34/0.56  fof(f113,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.34/0.56    inference(forward_demodulation,[],[f112,f83])).
% 1.34/0.56  fof(f112,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 1.34/0.56    inference(subsumption_resolution,[],[f111,f42])).
% 1.34/0.56  fof(f111,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.34/0.56    inference(superposition,[],[f57,f44])).
% 1.34/0.56  fof(f1491,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X1),X0)),X1),X0)) )),
% 1.34/0.56    inference(superposition,[],[f1428,f539])).
% 1.34/0.56  fof(f539,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),k9_relat_1(k6_relat_1(X0),X1)))) )),
% 1.34/0.56    inference(superposition,[],[f187,f146])).
% 1.34/0.56  fof(f146,plain,(
% 1.34/0.56    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(k9_relat_1(k6_relat_1(X3),X4)))) )),
% 1.34/0.56    inference(backward_demodulation,[],[f92,f140])).
% 1.34/0.56  fof(f92,plain,(
% 1.34/0.56    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4))))) )),
% 1.34/0.56    inference(resolution,[],[f90,f46])).
% 1.34/0.56  fof(f46,plain,(
% 1.34/0.56    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.34/0.56    inference(cnf_transformation,[],[f26])).
% 1.34/0.56  fof(f26,plain,(
% 1.34/0.56    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.34/0.56    inference(ennf_transformation,[],[f20])).
% 1.34/0.56  fof(f20,axiom,(
% 1.34/0.56    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.34/0.56  fof(f619,plain,(
% 1.34/0.56    ( ! [X2,X3] : (k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3)) )),
% 1.34/0.56    inference(resolution,[],[f617,f113])).
% 1.34/0.56  fof(f617,plain,(
% 1.34/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X0)) )),
% 1.34/0.56    inference(forward_demodulation,[],[f616,f140])).
% 1.34/0.56  fof(f616,plain,(
% 1.34/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X0)) )),
% 1.34/0.56    inference(forward_demodulation,[],[f601,f184])).
% 1.34/0.56  fof(f601,plain,(
% 1.34/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0)) )),
% 1.34/0.56    inference(superposition,[],[f557,f227])).
% 1.34/0.56  fof(f557,plain,(
% 1.34/0.56    ( ! [X4,X2,X3] : (r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X4))),X4)) )),
% 1.34/0.56    inference(subsumption_resolution,[],[f541,f90])).
% 1.34/0.56  fof(f541,plain,(
% 1.34/0.56    ( ! [X4,X2,X3] : (r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X4))),X4) | ~v1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) )),
% 1.34/0.56    inference(superposition,[],[f103,f187])).
% 1.34/0.56  fof(f103,plain,(
% 1.34/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))),X0) | ~v1_relat_1(X1)) )),
% 1.34/0.56    inference(subsumption_resolution,[],[f96,f42])).
% 1.34/0.56  fof(f96,plain,(
% 1.34/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))),X0) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.34/0.56    inference(superposition,[],[f47,f45])).
% 1.34/0.56  fof(f1640,plain,(
% 1.34/0.56    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k9_relat_1(k6_relat_1(sK1),sK0))),
% 1.34/0.56    inference(backward_demodulation,[],[f203,f1621])).
% 1.34/0.56  fof(f1621,plain,(
% 1.34/0.56    ( ! [X24,X25] : (k1_relat_1(k7_relat_1(k6_relat_1(X24),X25)) = k9_relat_1(k6_relat_1(X25),X24)) )),
% 1.34/0.56    inference(forward_demodulation,[],[f1614,f1531])).
% 1.34/0.56  fof(f1531,plain,(
% 1.34/0.56    ( ! [X37,X36] : (k9_relat_1(k6_relat_1(X37),X36) = k9_relat_1(k7_relat_1(k6_relat_1(X37),X36),X36)) )),
% 1.34/0.56    inference(backward_demodulation,[],[f664,f1521])).
% 1.34/0.56  fof(f664,plain,(
% 1.34/0.56    ( ! [X37,X36] : (k9_relat_1(k6_relat_1(X37),X36) = k9_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X37),X36)),X36)) )),
% 1.34/0.56    inference(forward_demodulation,[],[f649,f654])).
% 1.34/0.56  fof(f654,plain,(
% 1.34/0.56    ( ! [X6,X7] : (k9_relat_1(k6_relat_1(X7),X6) = k9_relat_1(k6_relat_1(X6),k9_relat_1(k6_relat_1(X7),X6))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f636,f45])).
% 1.34/0.56  fof(f636,plain,(
% 1.34/0.56    ( ! [X6,X7] : (k9_relat_1(k6_relat_1(X6),k9_relat_1(k6_relat_1(X7),X6)) = k2_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X7),X6)))) )),
% 1.34/0.56    inference(superposition,[],[f140,f618])).
% 1.34/0.56  fof(f618,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X1))) )),
% 1.34/0.56    inference(resolution,[],[f617,f127])).
% 1.34/0.56  fof(f127,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 1.34/0.56    inference(forward_demodulation,[],[f126,f83])).
% 1.34/0.56  fof(f126,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f123,f45])).
% 1.34/0.56  fof(f123,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 1.34/0.56    inference(resolution,[],[f58,f42])).
% 1.34/0.56  fof(f58,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 1.34/0.56    inference(cnf_transformation,[],[f36])).
% 1.34/0.56  fof(f36,plain,(
% 1.34/0.56    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.34/0.56    inference(flattening,[],[f35])).
% 1.34/0.56  fof(f35,plain,(
% 1.34/0.56    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.34/0.56    inference(ennf_transformation,[],[f19])).
% 1.34/0.56  fof(f19,axiom,(
% 1.34/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 1.34/0.56  fof(f649,plain,(
% 1.34/0.56    ( ! [X37,X36] : (k9_relat_1(k6_relat_1(X36),k9_relat_1(k6_relat_1(X37),X36)) = k9_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X37),X36)),X36)) )),
% 1.34/0.56    inference(superposition,[],[f277,f618])).
% 1.34/0.56  fof(f277,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.34/0.56    inference(forward_demodulation,[],[f275,f140])).
% 1.34/0.56  fof(f275,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.34/0.56    inference(superposition,[],[f147,f227])).
% 1.34/0.56  fof(f147,plain,(
% 1.34/0.56    ( ! [X6,X7,X5] : (k9_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f139,f91])).
% 1.34/0.56  fof(f139,plain,(
% 1.34/0.56    ( ! [X6,X7,X5] : (k2_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k9_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) )),
% 1.34/0.56    inference(resolution,[],[f136,f90])).
% 1.34/0.56  fof(f1614,plain,(
% 1.34/0.56    ( ! [X24,X25] : (k1_relat_1(k7_relat_1(k6_relat_1(X24),X25)) = k9_relat_1(k7_relat_1(k6_relat_1(X25),X24),X24)) )),
% 1.34/0.56    inference(backward_demodulation,[],[f323,f1609])).
% 1.34/0.56  fof(f1609,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 1.34/0.56    inference(backward_demodulation,[],[f199,f1608])).
% 1.34/0.56  fof(f1608,plain,(
% 1.34/0.56    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 1.34/0.56    inference(backward_demodulation,[],[f1549,f1562])).
% 1.34/0.56  fof(f1562,plain,(
% 1.34/0.56    ( ! [X15,X16] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X16),X15))) = k7_relat_1(k6_relat_1(X15),k1_relat_1(k7_relat_1(k6_relat_1(X16),X15)))) )),
% 1.34/0.56    inference(superposition,[],[f198,f1546])).
% 1.34/0.56  fof(f198,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 1.34/0.56    inference(backward_demodulation,[],[f128,f197])).
% 1.34/0.56  fof(f128,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.34/0.56    inference(resolution,[],[f127,f76])).
% 1.34/0.56  fof(f1549,plain,(
% 1.34/0.56    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2)) )),
% 1.34/0.56    inference(backward_demodulation,[],[f1519,f1546])).
% 1.34/0.56  fof(f1519,plain,(
% 1.34/0.56    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3),X2)) )),
% 1.34/0.56    inference(forward_demodulation,[],[f1490,f184])).
% 1.34/0.56  fof(f1490,plain,(
% 1.34/0.56    ( ! [X2,X3] : (k4_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3),X2)) )),
% 1.34/0.56    inference(superposition,[],[f1428,f1007])).
% 1.34/0.56  fof(f1007,plain,(
% 1.34/0.56    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) )),
% 1.34/0.56    inference(superposition,[],[f116,f91])).
% 1.34/0.56  fof(f116,plain,(
% 1.34/0.56    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))),k7_relat_1(k6_relat_1(X3),X4))) )),
% 1.34/0.56    inference(resolution,[],[f110,f90])).
% 1.34/0.56  fof(f110,plain,(
% 1.34/0.56    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 1.34/0.56    inference(resolution,[],[f57,f99])).
% 1.34/0.56  fof(f99,plain,(
% 1.34/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.34/0.56    inference(forward_demodulation,[],[f98,f45])).
% 1.34/0.56  fof(f98,plain,(
% 1.34/0.56    ( ! [X0] : (r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)))) )),
% 1.34/0.56    inference(subsumption_resolution,[],[f97,f42])).
% 1.34/0.56  fof(f97,plain,(
% 1.34/0.56    ( ! [X0] : (r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.34/0.56    inference(duplicate_literal_removal,[],[f94])).
% 1.34/0.56  fof(f94,plain,(
% 1.34/0.56    ( ! [X0] : (r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.34/0.56    inference(superposition,[],[f47,f80])).
% 1.34/0.56  fof(f80,plain,(
% 1.34/0.56    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f78,f45])).
% 1.34/0.56  fof(f78,plain,(
% 1.34/0.56    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) )),
% 1.34/0.56    inference(resolution,[],[f46,f42])).
% 1.34/0.56  fof(f199,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0)) )),
% 1.34/0.56    inference(backward_demodulation,[],[f118,f197])).
% 1.34/0.56  fof(f118,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))),X0)) )),
% 1.34/0.56    inference(resolution,[],[f113,f76])).
% 1.34/0.56  fof(f323,plain,(
% 1.34/0.56    ( ! [X24,X25] : (k1_relat_1(k7_relat_1(k6_relat_1(X24),X25)) = k9_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X24),X25))),X24)) )),
% 1.34/0.56    inference(forward_demodulation,[],[f314,f319])).
% 1.34/0.56  fof(f319,plain,(
% 1.34/0.56    ( ! [X6,X5] : (k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)) = k9_relat_1(k6_relat_1(X5),k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f306,f45])).
% 1.34/0.56  fof(f306,plain,(
% 1.34/0.56    ( ! [X6,X5] : (k9_relat_1(k6_relat_1(X5),k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) = k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))))) )),
% 1.34/0.56    inference(superposition,[],[f140,f198])).
% 1.34/0.56  fof(f314,plain,(
% 1.34/0.56    ( ! [X24,X25] : (k9_relat_1(k6_relat_1(X24),k1_relat_1(k7_relat_1(k6_relat_1(X24),X25))) = k9_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X24),X25))),X24)) )),
% 1.34/0.56    inference(superposition,[],[f277,f198])).
% 1.34/0.56  fof(f203,plain,(
% 1.34/0.56    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 1.34/0.56    inference(backward_demodulation,[],[f85,f197])).
% 1.34/0.56  fof(f85,plain,(
% 1.34/0.56    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.34/0.56    inference(backward_demodulation,[],[f75,f83])).
% 1.34/0.56  fof(f75,plain,(
% 1.34/0.56    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.34/0.56    inference(backward_demodulation,[],[f71,f73])).
% 1.34/0.56  fof(f71,plain,(
% 1.34/0.56    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 1.34/0.56    inference(definition_unfolding,[],[f41,f70])).
% 1.34/0.56  fof(f41,plain,(
% 1.34/0.56    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.34/0.56    inference(cnf_transformation,[],[f40])).
% 1.34/0.56  fof(f40,plain,(
% 1.34/0.56    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.34/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f39])).
% 1.34/0.56  fof(f39,plain,(
% 1.34/0.56    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.34/0.56    introduced(choice_axiom,[])).
% 1.34/0.56  fof(f25,plain,(
% 1.34/0.56    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.34/0.56    inference(ennf_transformation,[],[f24])).
% 1.34/0.56  fof(f24,negated_conjecture,(
% 1.34/0.56    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.34/0.56    inference(negated_conjecture,[],[f23])).
% 1.34/0.56  fof(f23,conjecture,(
% 1.34/0.56    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.34/0.56  % SZS output end Proof for theBenchmark
% 1.34/0.56  % (22000)------------------------------
% 1.34/0.56  % (22000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (22000)Termination reason: Refutation
% 1.34/0.56  
% 1.34/0.56  % (22000)Memory used [KB]: 7164
% 1.34/0.56  % (22000)Time elapsed: 0.118 s
% 1.34/0.56  % (22000)------------------------------
% 1.34/0.56  % (22000)------------------------------
% 1.34/0.56  % (21984)Success in time 0.185 s
%------------------------------------------------------------------------------
