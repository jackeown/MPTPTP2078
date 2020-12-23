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
% DateTime   : Thu Dec  3 12:52:24 EST 2020

% Result     : Theorem 4.68s
% Output     : Refutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :  142 (2524 expanded)
%              Number of leaves         :   24 ( 760 expanded)
%              Depth                    :   28
%              Number of atoms          :  212 (3657 expanded)
%              Number of equality atoms :  106 (1768 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8951,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8775,f7617])).

fof(f7617,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f7600,f1037])).

fof(f1037,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3) ),
    inference(forward_demodulation,[],[f1017,f152])).

fof(f152,plain,(
    ! [X6,X5] : k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)),X5) ),
    inference(resolution,[],[f138,f131])).

fof(f131,plain,(
    ! [X2,X1] : r1_tarski(k9_relat_1(k6_relat_1(X2),X1),X2) ),
    inference(forward_demodulation,[],[f130,f100])).

fof(f100,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f58,f45])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f130,plain,(
    ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2) ),
    inference(forward_demodulation,[],[f129,f47])).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f129,plain,(
    ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2))) ),
    inference(subsumption_resolution,[],[f128,f45])).

fof(f128,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f122,f45])).

fof(f122,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f49,f96])).

fof(f96,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f57,f45])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f137,f96])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f136,f45])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f62,f46])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f1017,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X2),X3) ),
    inference(superposition,[],[f115,f447])).

fof(f447,plain,(
    ! [X6,X8,X7] : k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8) ),
    inference(backward_demodulation,[],[f113,f446])).

fof(f446,plain,(
    ! [X6,X4,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5) = k8_relat_1(X4,k7_relat_1(k6_relat_1(X6),X5)) ),
    inference(forward_demodulation,[],[f445,f96])).

fof(f445,plain,(
    ! [X6,X4,X5] : k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5) ),
    inference(forward_demodulation,[],[f441,f112])).

fof(f112,plain,(
    ! [X4,X5,X3] : k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4)) ),
    inference(resolution,[],[f110,f57])).

fof(f110,plain,(
    ! [X6,X5] : v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) ),
    inference(subsumption_resolution,[],[f109,f45])).

fof(f109,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(subsumption_resolution,[],[f106,f45])).

fof(f106,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
      | ~ v1_relat_1(k6_relat_1(X6))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(superposition,[],[f65,f96])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f441,plain,(
    ! [X6,X4,X5] : k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X4),X6)) ),
    inference(resolution,[],[f301,f45])).

fof(f301,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X5)
      | k8_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6))) = k5_relat_1(X5,k7_relat_1(k6_relat_1(X4),X6)) ) ),
    inference(forward_demodulation,[],[f297,f98])).

fof(f98,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f93,f96])).

fof(f93,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f56,f45])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f297,plain,(
    ! [X6,X4,X5] :
      ( k8_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6))) = k5_relat_1(X5,k8_relat_1(X4,k6_relat_1(X6)))
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f63,f45])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(f113,plain,(
    ! [X6,X8,X7] : k8_relat_1(X6,k7_relat_1(k6_relat_1(X7),X8)) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6)) ),
    inference(resolution,[],[f110,f56])).

fof(f115,plain,(
    ! [X10,X9] : k7_relat_1(k6_relat_1(X9),X10) = k5_relat_1(k7_relat_1(k6_relat_1(X9),X10),k6_relat_1(k9_relat_1(k6_relat_1(X9),X10))) ),
    inference(forward_demodulation,[],[f114,f100])).

fof(f114,plain,(
    ! [X10,X9] : k7_relat_1(k6_relat_1(X9),X10) = k5_relat_1(k7_relat_1(k6_relat_1(X9),X10),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X9),X10)))) ),
    inference(resolution,[],[f110,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f7600,plain,(
    ! [X0,X1] : k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)),X1) ),
    inference(resolution,[],[f7593,f138])).

fof(f7593,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1) ),
    inference(superposition,[],[f7277,f242])).

fof(f242,plain,(
    ! [X2,X3] : k9_relat_1(k6_relat_1(X2),X3) = k9_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2) ),
    inference(forward_demodulation,[],[f241,f100])).

fof(f241,plain,(
    ! [X2,X3] : k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k9_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2) ),
    inference(superposition,[],[f111,f214])).

fof(f214,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(superposition,[],[f112,f185])).

fof(f185,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(subsumption_resolution,[],[f181,f110])).

fof(f181,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f176,f62])).

fof(f176,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    inference(backward_demodulation,[],[f83,f174])).

fof(f174,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f171,f46])).

fof(f171,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(resolution,[],[f84,f45])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(forward_demodulation,[],[f81,f80])).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f68,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f59,f76])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f78,f80])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f51,f76])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f111,plain,(
    ! [X2,X0,X1] : k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(resolution,[],[f110,f58])).

fof(f7277,plain,(
    ! [X85,X83,X84] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X84),X83),X85),X83) ),
    inference(superposition,[],[f462,f7007])).

fof(f7007,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(superposition,[],[f6852,f46])).

fof(f6852,plain,(
    ! [X171,X172] : k7_relat_1(k6_relat_1(X171),X172) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X172),X171))) ),
    inference(forward_demodulation,[],[f6851,f485])).

fof(f485,plain,(
    ! [X0,X1] : k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(resolution,[],[f480,f138])).

fof(f480,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[],[f449,f214])).

fof(f449,plain,(
    ! [X4,X5,X3] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4)) ),
    inference(backward_demodulation,[],[f268,f446])).

fof(f268,plain,(
    ! [X4,X5,X3] : r1_tarski(k8_relat_1(X5,k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4)) ),
    inference(subsumption_resolution,[],[f262,f110])).

fof(f262,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k8_relat_1(X5,k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(superposition,[],[f60,f113])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f6851,plain,(
    ! [X171,X172] : k7_relat_1(k6_relat_1(X171),X172) = k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X172),X171)),k7_relat_1(k6_relat_1(X171),X172))) ),
    inference(forward_demodulation,[],[f6727,f46])).

fof(f6727,plain,(
    ! [X171,X172] : k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X172),X171)),k7_relat_1(k6_relat_1(X171),X172))) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X171),X172))) ),
    inference(superposition,[],[f1733,f485])).

fof(f1733,plain,(
    ! [X2,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) ),
    inference(superposition,[],[f1424,f177])).

fof(f177,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(backward_demodulation,[],[f80,f174])).

fof(f1424,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(superposition,[],[f177,f79])).

fof(f79,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f52,f75,f75])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f462,plain,(
    ! [X2,X0,X1] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),X2) ),
    inference(forward_demodulation,[],[f448,f111])).

fof(f448,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)),X2) ),
    inference(backward_demodulation,[],[f267,f446])).

fof(f267,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_relat_1(k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1))),X2) ),
    inference(subsumption_resolution,[],[f261,f110])).

fof(f261,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1))),X2)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(superposition,[],[f132,f113])).

fof(f132,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f123,f45])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))),X0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f49,f47])).

fof(f8775,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k9_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(backward_demodulation,[],[f179,f8425])).

fof(f8425,plain,(
    ! [X2,X3] : k9_relat_1(k6_relat_1(X2),X3) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) ),
    inference(superposition,[],[f46,f7617])).

fof(f179,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(backward_demodulation,[],[f99,f174])).

fof(f99,plain,(
    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f95,f98])).

fof(f95,plain,(
    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f82,f93])).

fof(f82,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f77,f80])).

fof(f77,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f44,f76])).

fof(f44,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f42])).

fof(f42,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:10:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (24386)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (24373)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (24372)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (24383)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (24385)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (24371)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (24379)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (24377)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (24380)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (24376)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (24375)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (24378)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (24374)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.52  % (24381)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.53  % (24382)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.54  % (24388)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.54  % (24384)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.54  % (24387)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.55  % (24382)Refutation not found, incomplete strategy% (24382)------------------------------
% 0.21/0.55  % (24382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24382)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24382)Memory used [KB]: 10618
% 0.21/0.55  % (24382)Time elapsed: 0.144 s
% 0.21/0.55  % (24382)------------------------------
% 0.21/0.55  % (24382)------------------------------
% 4.68/1.01  % (24380)Refutation found. Thanks to Tanya!
% 4.68/1.01  % SZS status Theorem for theBenchmark
% 4.68/1.01  % SZS output start Proof for theBenchmark
% 4.68/1.01  fof(f8951,plain,(
% 4.68/1.01    $false),
% 4.68/1.01    inference(subsumption_resolution,[],[f8775,f7617])).
% 4.68/1.01  fof(f7617,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k9_relat_1(k6_relat_1(X0),X1))) )),
% 4.68/1.01    inference(forward_demodulation,[],[f7600,f1037])).
% 4.68/1.01  fof(f1037,plain,(
% 4.68/1.01    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3)) )),
% 4.68/1.01    inference(forward_demodulation,[],[f1017,f152])).
% 4.68/1.01  fof(f152,plain,(
% 4.68/1.01    ( ! [X6,X5] : (k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)),X5)) )),
% 4.68/1.01    inference(resolution,[],[f138,f131])).
% 4.68/1.01  fof(f131,plain,(
% 4.68/1.01    ( ! [X2,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X2),X1),X2)) )),
% 4.68/1.01    inference(forward_demodulation,[],[f130,f100])).
% 4.68/1.01  fof(f100,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 4.68/1.01    inference(resolution,[],[f58,f45])).
% 4.68/1.01  fof(f45,plain,(
% 4.68/1.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 4.68/1.01    inference(cnf_transformation,[],[f12])).
% 4.68/1.01  fof(f12,axiom,(
% 4.68/1.01    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 4.68/1.01  fof(f58,plain,(
% 4.68/1.01    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f33])).
% 4.68/1.01  fof(f33,plain,(
% 4.68/1.01    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.68/1.01    inference(ennf_transformation,[],[f16])).
% 4.68/1.01  fof(f16,axiom,(
% 4.68/1.01    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 4.68/1.01  fof(f130,plain,(
% 4.68/1.01    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2)) )),
% 4.68/1.01    inference(forward_demodulation,[],[f129,f47])).
% 4.68/1.01  fof(f47,plain,(
% 4.68/1.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 4.68/1.01    inference(cnf_transformation,[],[f19])).
% 4.68/1.01  fof(f19,axiom,(
% 4.68/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 4.68/1.01  fof(f129,plain,(
% 4.68/1.01    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))) )),
% 4.68/1.01    inference(subsumption_resolution,[],[f128,f45])).
% 4.68/1.01  fof(f128,plain,(
% 4.68/1.01    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 4.68/1.01    inference(subsumption_resolution,[],[f122,f45])).
% 4.68/1.01  fof(f122,plain,(
% 4.68/1.01    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 4.68/1.01    inference(superposition,[],[f49,f96])).
% 4.68/1.01  fof(f96,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 4.68/1.01    inference(resolution,[],[f57,f45])).
% 4.68/1.01  fof(f57,plain,(
% 4.68/1.01    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f32])).
% 4.68/1.01  fof(f32,plain,(
% 4.68/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 4.68/1.01    inference(ennf_transformation,[],[f24])).
% 4.68/1.01  fof(f24,axiom,(
% 4.68/1.01    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 4.68/1.01  fof(f49,plain,(
% 4.68/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f29])).
% 4.68/1.01  fof(f29,plain,(
% 4.68/1.01    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.68/1.01    inference(ennf_transformation,[],[f17])).
% 4.68/1.01  fof(f17,axiom,(
% 4.68/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 4.68/1.01  fof(f138,plain,(
% 4.68/1.01    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 4.68/1.01    inference(forward_demodulation,[],[f137,f96])).
% 4.68/1.01  fof(f137,plain,(
% 4.68/1.01    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 4.68/1.01    inference(subsumption_resolution,[],[f136,f45])).
% 4.68/1.01  fof(f136,plain,(
% 4.68/1.01    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 4.68/1.01    inference(superposition,[],[f62,f46])).
% 4.68/1.01  fof(f46,plain,(
% 4.68/1.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 4.68/1.01    inference(cnf_transformation,[],[f19])).
% 4.68/1.01  fof(f62,plain,(
% 4.68/1.01    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f37])).
% 4.68/1.01  fof(f37,plain,(
% 4.68/1.01    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.68/1.01    inference(flattening,[],[f36])).
% 4.68/1.01  fof(f36,plain,(
% 4.68/1.01    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.68/1.01    inference(ennf_transformation,[],[f21])).
% 4.68/1.01  fof(f21,axiom,(
% 4.68/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 4.68/1.01  fof(f1017,plain,(
% 4.68/1.01    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X2),X3)) )),
% 4.68/1.01    inference(superposition,[],[f115,f447])).
% 4.68/1.01  fof(f447,plain,(
% 4.68/1.01    ( ! [X6,X8,X7] : (k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8)) )),
% 4.68/1.01    inference(backward_demodulation,[],[f113,f446])).
% 4.68/1.01  fof(f446,plain,(
% 4.68/1.01    ( ! [X6,X4,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5) = k8_relat_1(X4,k7_relat_1(k6_relat_1(X6),X5))) )),
% 4.68/1.01    inference(forward_demodulation,[],[f445,f96])).
% 4.68/1.01  fof(f445,plain,(
% 4.68/1.01    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5)) )),
% 4.68/1.01    inference(forward_demodulation,[],[f441,f112])).
% 4.68/1.01  fof(f112,plain,(
% 4.68/1.01    ( ! [X4,X5,X3] : (k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4))) )),
% 4.68/1.01    inference(resolution,[],[f110,f57])).
% 4.68/1.01  fof(f110,plain,(
% 4.68/1.01    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))) )),
% 4.68/1.01    inference(subsumption_resolution,[],[f109,f45])).
% 4.68/1.01  fof(f109,plain,(
% 4.68/1.01    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) | ~v1_relat_1(k6_relat_1(X5))) )),
% 4.68/1.01    inference(subsumption_resolution,[],[f106,f45])).
% 4.68/1.01  fof(f106,plain,(
% 4.68/1.01    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(k6_relat_1(X5))) )),
% 4.68/1.01    inference(superposition,[],[f65,f96])).
% 4.68/1.01  fof(f65,plain,(
% 4.68/1.01    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f41])).
% 4.68/1.01  fof(f41,plain,(
% 4.68/1.01    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 4.68/1.01    inference(flattening,[],[f40])).
% 4.68/1.01  fof(f40,plain,(
% 4.68/1.01    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 4.68/1.01    inference(ennf_transformation,[],[f11])).
% 4.68/1.01  fof(f11,axiom,(
% 4.68/1.01    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 4.68/1.01  fof(f441,plain,(
% 4.68/1.01    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X4),X6))) )),
% 4.68/1.01    inference(resolution,[],[f301,f45])).
% 4.68/1.01  fof(f301,plain,(
% 4.68/1.01    ( ! [X6,X4,X5] : (~v1_relat_1(X5) | k8_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6))) = k5_relat_1(X5,k7_relat_1(k6_relat_1(X4),X6))) )),
% 4.68/1.01    inference(forward_demodulation,[],[f297,f98])).
% 4.68/1.01  fof(f98,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 4.68/1.01    inference(backward_demodulation,[],[f93,f96])).
% 4.68/1.01  fof(f93,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 4.68/1.01    inference(resolution,[],[f56,f45])).
% 4.68/1.01  fof(f56,plain,(
% 4.68/1.01    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 4.68/1.01    inference(cnf_transformation,[],[f31])).
% 4.68/1.01  fof(f31,plain,(
% 4.68/1.01    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 4.68/1.01    inference(ennf_transformation,[],[f14])).
% 4.68/1.01  fof(f14,axiom,(
% 4.68/1.01    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 4.68/1.01  fof(f297,plain,(
% 4.68/1.01    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6))) = k5_relat_1(X5,k8_relat_1(X4,k6_relat_1(X6))) | ~v1_relat_1(X5)) )),
% 4.68/1.01    inference(resolution,[],[f63,f45])).
% 4.68/1.01  fof(f63,plain,(
% 4.68/1.01    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X1)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f38])).
% 4.68/1.01  fof(f38,plain,(
% 4.68/1.01    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.68/1.01    inference(ennf_transformation,[],[f15])).
% 4.68/1.01  fof(f15,axiom,(
% 4.68/1.01    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).
% 4.68/1.01  fof(f113,plain,(
% 4.68/1.01    ( ! [X6,X8,X7] : (k8_relat_1(X6,k7_relat_1(k6_relat_1(X7),X8)) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6))) )),
% 4.68/1.01    inference(resolution,[],[f110,f56])).
% 4.68/1.01  fof(f115,plain,(
% 4.68/1.01    ( ! [X10,X9] : (k7_relat_1(k6_relat_1(X9),X10) = k5_relat_1(k7_relat_1(k6_relat_1(X9),X10),k6_relat_1(k9_relat_1(k6_relat_1(X9),X10)))) )),
% 4.68/1.01    inference(forward_demodulation,[],[f114,f100])).
% 4.68/1.01  fof(f114,plain,(
% 4.68/1.01    ( ! [X10,X9] : (k7_relat_1(k6_relat_1(X9),X10) = k5_relat_1(k7_relat_1(k6_relat_1(X9),X10),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X9),X10))))) )),
% 4.68/1.01    inference(resolution,[],[f110,f48])).
% 4.68/1.01  fof(f48,plain,(
% 4.68/1.01    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 4.68/1.01    inference(cnf_transformation,[],[f28])).
% 4.68/1.01  fof(f28,plain,(
% 4.68/1.01    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 4.68/1.01    inference(ennf_transformation,[],[f22])).
% 4.68/1.01  fof(f22,axiom,(
% 4.68/1.01    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 4.68/1.01  fof(f7600,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)),X1)) )),
% 4.68/1.01    inference(resolution,[],[f7593,f138])).
% 4.68/1.01  fof(f7593,plain,(
% 4.68/1.01    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1)) )),
% 4.68/1.01    inference(superposition,[],[f7277,f242])).
% 4.68/1.01  fof(f242,plain,(
% 4.68/1.01    ( ! [X2,X3] : (k9_relat_1(k6_relat_1(X2),X3) = k9_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2)) )),
% 4.68/1.01    inference(forward_demodulation,[],[f241,f100])).
% 4.68/1.01  fof(f241,plain,(
% 4.68/1.01    ( ! [X2,X3] : (k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k9_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2)) )),
% 4.68/1.01    inference(superposition,[],[f111,f214])).
% 4.68/1.01  fof(f214,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 4.68/1.01    inference(superposition,[],[f112,f185])).
% 4.68/1.01  fof(f185,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) )),
% 4.68/1.01    inference(subsumption_resolution,[],[f181,f110])).
% 4.68/1.01  fof(f181,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 4.68/1.01    inference(resolution,[],[f176,f62])).
% 4.68/1.01  fof(f176,plain,(
% 4.68/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) )),
% 4.68/1.01    inference(backward_demodulation,[],[f83,f174])).
% 4.68/1.01  fof(f174,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 4.68/1.01    inference(forward_demodulation,[],[f171,f46])).
% 4.68/1.01  fof(f171,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) )),
% 4.68/1.01    inference(resolution,[],[f84,f45])).
% 4.68/1.01  fof(f84,plain,(
% 4.68/1.01    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) )),
% 4.68/1.01    inference(forward_demodulation,[],[f81,f80])).
% 4.68/1.01  fof(f80,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 4.68/1.01    inference(definition_unfolding,[],[f55,f76])).
% 4.68/1.01  fof(f76,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 4.68/1.01    inference(definition_unfolding,[],[f54,f75])).
% 4.68/1.01  fof(f75,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 4.68/1.01    inference(definition_unfolding,[],[f53,f74])).
% 4.68/1.01  fof(f74,plain,(
% 4.68/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 4.68/1.01    inference(definition_unfolding,[],[f66,f73])).
% 4.68/1.01  fof(f73,plain,(
% 4.68/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 4.68/1.01    inference(definition_unfolding,[],[f67,f72])).
% 4.68/1.01  fof(f72,plain,(
% 4.68/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.68/1.01    inference(definition_unfolding,[],[f68,f71])).
% 4.68/1.01  fof(f71,plain,(
% 4.68/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.68/1.01    inference(definition_unfolding,[],[f69,f70])).
% 4.68/1.01  fof(f70,plain,(
% 4.68/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f9])).
% 4.68/1.01  fof(f9,axiom,(
% 4.68/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 4.68/1.01  fof(f69,plain,(
% 4.68/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f8])).
% 4.68/1.01  fof(f8,axiom,(
% 4.68/1.01    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 4.68/1.01  fof(f68,plain,(
% 4.68/1.01    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f7])).
% 4.68/1.01  fof(f7,axiom,(
% 4.68/1.01    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 4.68/1.01  fof(f67,plain,(
% 4.68/1.01    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f6])).
% 4.68/1.01  fof(f6,axiom,(
% 4.68/1.01    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 4.68/1.01  fof(f66,plain,(
% 4.68/1.01    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f5])).
% 4.68/1.01  fof(f5,axiom,(
% 4.68/1.01    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 4.68/1.01  fof(f53,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f4])).
% 4.68/1.01  fof(f4,axiom,(
% 4.68/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 4.68/1.01  fof(f54,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.68/1.01    inference(cnf_transformation,[],[f10])).
% 4.68/1.01  fof(f10,axiom,(
% 4.68/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 4.68/1.01  fof(f55,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.68/1.01    inference(cnf_transformation,[],[f2])).
% 4.68/1.01  fof(f2,axiom,(
% 4.68/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.68/1.01  fof(f81,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 4.68/1.01    inference(definition_unfolding,[],[f59,f76])).
% 4.68/1.01  fof(f59,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f34])).
% 4.68/1.01  fof(f34,plain,(
% 4.68/1.01    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.68/1.01    inference(ennf_transformation,[],[f23])).
% 4.68/1.01  fof(f23,axiom,(
% 4.68/1.01    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 4.68/1.01  fof(f83,plain,(
% 4.68/1.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 4.68/1.01    inference(backward_demodulation,[],[f78,f80])).
% 4.68/1.01  fof(f78,plain,(
% 4.68/1.01    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 4.68/1.01    inference(definition_unfolding,[],[f51,f76])).
% 4.68/1.01  fof(f51,plain,(
% 4.68/1.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f1])).
% 4.68/1.01  fof(f1,axiom,(
% 4.68/1.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 4.68/1.01  fof(f111,plain,(
% 4.68/1.01    ( ! [X2,X0,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) )),
% 4.68/1.01    inference(resolution,[],[f110,f58])).
% 4.68/1.01  fof(f7277,plain,(
% 4.68/1.01    ( ! [X85,X83,X84] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X84),X83),X85),X83)) )),
% 4.68/1.01    inference(superposition,[],[f462,f7007])).
% 4.68/1.01  fof(f7007,plain,(
% 4.68/1.01    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 4.68/1.01    inference(superposition,[],[f6852,f46])).
% 4.68/1.01  fof(f6852,plain,(
% 4.68/1.01    ( ! [X171,X172] : (k7_relat_1(k6_relat_1(X171),X172) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X172),X171)))) )),
% 4.68/1.01    inference(forward_demodulation,[],[f6851,f485])).
% 4.68/1.01  fof(f485,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k6_relat_1(X1),X0))) )),
% 4.68/1.01    inference(resolution,[],[f480,f138])).
% 4.68/1.01  fof(f480,plain,(
% 4.68/1.01    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0))) )),
% 4.68/1.01    inference(superposition,[],[f449,f214])).
% 4.68/1.01  fof(f449,plain,(
% 4.68/1.01    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))) )),
% 4.68/1.01    inference(backward_demodulation,[],[f268,f446])).
% 4.68/1.01  fof(f268,plain,(
% 4.68/1.01    ( ! [X4,X5,X3] : (r1_tarski(k8_relat_1(X5,k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4))) )),
% 4.68/1.01    inference(subsumption_resolution,[],[f262,f110])).
% 4.68/1.01  fof(f262,plain,(
% 4.68/1.01    ( ! [X4,X5,X3] : (r1_tarski(k8_relat_1(X5,k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) )),
% 4.68/1.01    inference(superposition,[],[f60,f113])).
% 4.68/1.01  fof(f60,plain,(
% 4.68/1.01    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f35])).
% 4.68/1.01  fof(f35,plain,(
% 4.68/1.01    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 4.68/1.01    inference(ennf_transformation,[],[f20])).
% 4.68/1.01  fof(f20,axiom,(
% 4.68/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 4.68/1.01  fof(f6851,plain,(
% 4.68/1.01    ( ! [X171,X172] : (k7_relat_1(k6_relat_1(X171),X172) = k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X172),X171)),k7_relat_1(k6_relat_1(X171),X172)))) )),
% 4.68/1.01    inference(forward_demodulation,[],[f6727,f46])).
% 4.68/1.01  fof(f6727,plain,(
% 4.68/1.01    ( ! [X171,X172] : (k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X172),X171)),k7_relat_1(k6_relat_1(X171),X172))) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X171),X172)))) )),
% 4.68/1.01    inference(superposition,[],[f1733,f485])).
% 4.68/1.01  fof(f1733,plain,(
% 4.68/1.01    ( ! [X2,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k1_relat_1(k7_relat_1(k6_relat_1(X3),X2))) )),
% 4.68/1.01    inference(superposition,[],[f1424,f177])).
% 4.68/1.01  fof(f177,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 4.68/1.01    inference(backward_demodulation,[],[f80,f174])).
% 4.68/1.01  fof(f1424,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )),
% 4.68/1.01    inference(superposition,[],[f177,f79])).
% 4.68/1.01  fof(f79,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 4.68/1.01    inference(definition_unfolding,[],[f52,f75,f75])).
% 4.68/1.01  fof(f52,plain,(
% 4.68/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 4.68/1.01    inference(cnf_transformation,[],[f3])).
% 4.68/1.01  fof(f3,axiom,(
% 4.68/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 4.68/1.01  fof(f462,plain,(
% 4.68/1.01    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),X2)) )),
% 4.68/1.01    inference(forward_demodulation,[],[f448,f111])).
% 4.68/1.01  fof(f448,plain,(
% 4.68/1.01    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)),X2)) )),
% 4.68/1.01    inference(backward_demodulation,[],[f267,f446])).
% 4.68/1.01  fof(f267,plain,(
% 4.68/1.01    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1))),X2)) )),
% 4.68/1.01    inference(subsumption_resolution,[],[f261,f110])).
% 4.68/1.01  fof(f261,plain,(
% 4.68/1.01    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1))),X2) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 4.68/1.01    inference(superposition,[],[f132,f113])).
% 4.68/1.01  fof(f132,plain,(
% 4.68/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))),X0) | ~v1_relat_1(X1)) )),
% 4.68/1.01    inference(subsumption_resolution,[],[f123,f45])).
% 4.68/1.01  fof(f123,plain,(
% 4.68/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))),X0) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 4.68/1.01    inference(superposition,[],[f49,f47])).
% 4.68/1.01  fof(f8775,plain,(
% 4.68/1.01    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k9_relat_1(k6_relat_1(sK0),sK1))),
% 4.68/1.01    inference(backward_demodulation,[],[f179,f8425])).
% 4.68/1.01  fof(f8425,plain,(
% 4.68/1.01    ( ! [X2,X3] : (k9_relat_1(k6_relat_1(X2),X3) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) )),
% 4.68/1.01    inference(superposition,[],[f46,f7617])).
% 4.68/1.01  fof(f179,plain,(
% 4.68/1.01    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 4.68/1.01    inference(backward_demodulation,[],[f99,f174])).
% 4.68/1.01  fof(f99,plain,(
% 4.68/1.01    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 4.68/1.01    inference(backward_demodulation,[],[f95,f98])).
% 4.68/1.01  fof(f95,plain,(
% 4.68/1.01    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 4.68/1.01    inference(backward_demodulation,[],[f82,f93])).
% 4.68/1.01  fof(f82,plain,(
% 4.68/1.01    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 4.68/1.01    inference(backward_demodulation,[],[f77,f80])).
% 4.68/1.01  fof(f77,plain,(
% 4.68/1.01    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 4.68/1.01    inference(definition_unfolding,[],[f44,f76])).
% 4.68/1.01  fof(f44,plain,(
% 4.68/1.01    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 4.68/1.01    inference(cnf_transformation,[],[f43])).
% 4.68/1.01  fof(f43,plain,(
% 4.68/1.01    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 4.68/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f42])).
% 4.68/1.01  fof(f42,plain,(
% 4.68/1.01    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 4.68/1.01    introduced(choice_axiom,[])).
% 4.68/1.01  fof(f27,plain,(
% 4.68/1.01    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 4.68/1.01    inference(ennf_transformation,[],[f26])).
% 4.68/1.01  fof(f26,negated_conjecture,(
% 4.68/1.01    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 4.68/1.01    inference(negated_conjecture,[],[f25])).
% 4.68/1.01  fof(f25,conjecture,(
% 4.68/1.01    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 4.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 4.68/1.01  % SZS output end Proof for theBenchmark
% 4.68/1.01  % (24380)------------------------------
% 4.68/1.01  % (24380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.68/1.01  % (24380)Termination reason: Refutation
% 4.68/1.01  
% 4.68/1.01  % (24380)Memory used [KB]: 15735
% 4.68/1.01  % (24380)Time elapsed: 0.575 s
% 4.68/1.01  % (24380)------------------------------
% 4.68/1.01  % (24380)------------------------------
% 4.68/1.02  % (24370)Success in time 0.658 s
%------------------------------------------------------------------------------
