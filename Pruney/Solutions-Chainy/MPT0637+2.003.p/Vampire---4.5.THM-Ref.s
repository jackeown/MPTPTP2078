%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:22 EST 2020

% Result     : Theorem 3.07s
% Output     : Refutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 516 expanded)
%              Number of leaves         :   24 ( 163 expanded)
%              Depth                    :   20
%              Number of atoms          :  195 ( 810 expanded)
%              Number of equality atoms :   83 ( 408 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5860,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f180,f240,f378,f5848])).

fof(f5848,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f5684])).

fof(f5684,plain,
    ( $false
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f377,f2866])).

fof(f2866,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(forward_demodulation,[],[f2814,f757])).

fof(f757,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X2),X1) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) ),
    inference(forward_demodulation,[],[f400,f410])).

fof(f410,plain,(
    ! [X12,X13] : k7_relat_1(k6_relat_1(X13),X12) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X12))),X12) ),
    inference(forward_demodulation,[],[f407,f332])).

fof(f332,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f331,f91])).

fof(f91,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(unit_resulting_resolution,[],[f45,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f331,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f140,f91])).

fof(f140,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f139,f44])).

fof(f44,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f139,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f131,f44])).

fof(f131,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f45,f45,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f407,plain,(
    ! [X12,X13] : k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X12))),X12) = k4_relat_1(k7_relat_1(k6_relat_1(X12),X13)) ),
    inference(superposition,[],[f332,f397])).

fof(f397,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(forward_demodulation,[],[f393,f48])).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f393,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X0))))) ),
    inference(unit_resulting_resolution,[],[f45,f371])).

fof(f371,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k2_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(X1)))) ) ),
    inference(backward_demodulation,[],[f77,f355])).

fof(f355,plain,(
    ! [X0,X1] : k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f155,f226])).

fof(f226,plain,(
    ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(backward_demodulation,[],[f89,f91])).

fof(f89,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f45,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f155,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0)) ),
    inference(forward_demodulation,[],[f151,f49])).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f151,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k4_enumset1(k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),X0)) ),
    inference(unit_resulting_resolution,[],[f45,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f58,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k4_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f59,f74])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f400,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))),X1) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) ),
    inference(superposition,[],[f397,f397])).

fof(f2814,plain,(
    ! [X0,X1] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(unit_resulting_resolution,[],[f474,f301])).

fof(f301,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f98,f226])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f97,f49])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(resolution,[],[f62,f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f474,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(forward_demodulation,[],[f464,f49])).

fof(f464,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))))) ),
    inference(unit_resulting_resolution,[],[f234,f45,f404,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f404,plain,(
    ! [X6,X7] : r1_tarski(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X7),X6)))) ),
    inference(superposition,[],[f233,f397])).

fof(f233,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0)) ),
    inference(backward_demodulation,[],[f169,f226])).

fof(f169,plain,(
    ! [X0,X1] : r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X0)) ),
    inference(backward_demodulation,[],[f83,f89])).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f45,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f234,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(backward_demodulation,[],[f172,f226])).

fof(f172,plain,(
    ! [X0,X1] : v1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(backward_demodulation,[],[f103,f89])).

fof(f103,plain,(
    ! [X0,X1] : v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f45,f87,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f87,plain,(
    ! [X0,X1] : m1_subset_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k1_zfmisc_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f83,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f377,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl2_4
  <=> k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f378,plain,
    ( ~ spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f373,f237,f375])).

fof(f237,plain,
    ( spl2_3
  <=> k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f373,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0)))
    | spl2_3 ),
    inference(backward_demodulation,[],[f239,f355])).

fof(f239,plain,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f237])).

fof(f240,plain,
    ( ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f235,f177,f237])).

fof(f177,plain,
    ( spl2_2
  <=> k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = k8_relat_1(sK0,k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f235,plain,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_2 ),
    inference(backward_demodulation,[],[f179,f226])).

fof(f179,plain,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f177])).

fof(f180,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f168,f79,f177])).

fof(f79,plain,
    ( spl2_1
  <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f168,plain,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))
    | spl2_1 ),
    inference(backward_demodulation,[],[f81,f89])).

fof(f81,plain,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f82,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f75,f79])).

fof(f75,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f43,f74])).

fof(f43,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f40])).

fof(f40,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (19127)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (19135)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (19130)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.52  % (19128)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.52  % (19129)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (19138)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.52  % (19131)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (19140)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.54  % (19132)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.54  % (19136)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.54  % (19137)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.54  % (19139)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.54  % (19136)Refutation not found, incomplete strategy% (19136)------------------------------
% 0.21/0.54  % (19136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19136)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19136)Memory used [KB]: 10618
% 0.21/0.54  % (19136)Time elapsed: 0.091 s
% 0.21/0.54  % (19136)------------------------------
% 0.21/0.54  % (19136)------------------------------
% 1.50/0.57  % (19133)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.50/0.57  % (19126)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.50/0.57  % (19142)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.73/0.58  % (19125)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.73/0.59  % (19134)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.73/0.60  % (19143)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 3.07/0.80  % (19131)Refutation found. Thanks to Tanya!
% 3.07/0.80  % SZS status Theorem for theBenchmark
% 3.07/0.80  % SZS output start Proof for theBenchmark
% 3.07/0.80  fof(f5860,plain,(
% 3.07/0.80    $false),
% 3.07/0.80    inference(avatar_sat_refutation,[],[f82,f180,f240,f378,f5848])).
% 3.07/0.80  fof(f5848,plain,(
% 3.07/0.80    spl2_4),
% 3.07/0.80    inference(avatar_contradiction_clause,[],[f5684])).
% 3.07/0.80  fof(f5684,plain,(
% 3.07/0.80    $false | spl2_4),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f377,f2866])).
% 3.07/0.80  fof(f2866,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 3.07/0.80    inference(forward_demodulation,[],[f2814,f757])).
% 3.07/0.80  fof(f757,plain,(
% 3.07/0.80    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X2),X1) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)))) )),
% 3.07/0.80    inference(forward_demodulation,[],[f400,f410])).
% 3.07/0.80  fof(f410,plain,(
% 3.07/0.80    ( ! [X12,X13] : (k7_relat_1(k6_relat_1(X13),X12) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X12))),X12)) )),
% 3.07/0.80    inference(forward_demodulation,[],[f407,f332])).
% 3.07/0.80  fof(f332,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 3.07/0.80    inference(forward_demodulation,[],[f331,f91])).
% 3.07/0.80  fof(f91,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f45,f57])).
% 3.07/0.80  fof(f57,plain,(
% 3.07/0.80    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 3.07/0.80    inference(cnf_transformation,[],[f30])).
% 3.07/0.80  fof(f30,plain,(
% 3.07/0.80    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.07/0.80    inference(ennf_transformation,[],[f20])).
% 3.07/0.80  fof(f20,axiom,(
% 3.07/0.80    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.07/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 3.07/0.80  fof(f45,plain,(
% 3.07/0.80    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.07/0.80    inference(cnf_transformation,[],[f21])).
% 3.07/0.80  fof(f21,axiom,(
% 3.07/0.80    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 3.07/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
% 3.07/0.80  fof(f331,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 3.07/0.80    inference(forward_demodulation,[],[f140,f91])).
% 3.07/0.80  fof(f140,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 3.07/0.80    inference(forward_demodulation,[],[f139,f44])).
% 3.07/0.80  fof(f44,plain,(
% 3.07/0.80    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 3.07/0.80    inference(cnf_transformation,[],[f18])).
% 3.07/0.80  fof(f18,axiom,(
% 3.07/0.80    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 3.07/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 3.07/0.80  fof(f139,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))) )),
% 3.07/0.80    inference(forward_demodulation,[],[f131,f44])).
% 3.07/0.80  fof(f131,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(k6_relat_1(X0)))) )),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f45,f45,f50])).
% 3.07/0.80  fof(f50,plain,(
% 3.07/0.80    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 3.07/0.80    inference(cnf_transformation,[],[f25])).
% 3.07/0.80  fof(f25,plain,(
% 3.07/0.80    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.07/0.80    inference(ennf_transformation,[],[f16])).
% 3.07/0.80  fof(f16,axiom,(
% 3.07/0.80    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 3.07/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 3.07/0.80  fof(f407,plain,(
% 3.07/0.80    ( ! [X12,X13] : (k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X12))),X12) = k4_relat_1(k7_relat_1(k6_relat_1(X12),X13))) )),
% 3.07/0.80    inference(superposition,[],[f332,f397])).
% 3.07/0.80  fof(f397,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) )),
% 3.07/0.80    inference(forward_demodulation,[],[f393,f48])).
% 3.07/0.80  fof(f48,plain,(
% 3.07/0.80    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.07/0.80    inference(cnf_transformation,[],[f17])).
% 3.07/0.80  fof(f17,axiom,(
% 3.07/0.80    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.07/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 3.07/0.80  fof(f393,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X0)))))) )),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f45,f371])).
% 3.07/0.80  fof(f371,plain,(
% 3.07/0.80    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k2_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(X1))))) )),
% 3.07/0.80    inference(backward_demodulation,[],[f77,f355])).
% 3.07/0.80  fof(f355,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 3.07/0.80    inference(forward_demodulation,[],[f155,f226])).
% 3.07/0.80  fof(f226,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 3.07/0.80    inference(backward_demodulation,[],[f89,f91])).
% 3.07/0.80  fof(f89,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f45,f56])).
% 3.07/0.80  fof(f56,plain,(
% 3.07/0.80    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 3.07/0.80    inference(cnf_transformation,[],[f29])).
% 3.07/0.80  fof(f29,plain,(
% 3.07/0.80    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 3.07/0.80    inference(ennf_transformation,[],[f10])).
% 3.07/0.80  fof(f10,axiom,(
% 3.07/0.80    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 3.07/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 3.07/0.80  fof(f155,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0))) )),
% 3.07/0.80    inference(forward_demodulation,[],[f151,f49])).
% 3.07/0.80  fof(f49,plain,(
% 3.07/0.80    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.07/0.80    inference(cnf_transformation,[],[f17])).
% 3.07/0.80  fof(f151,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k4_enumset1(k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),X0))) )),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f45,f76])).
% 3.07/0.80  fof(f76,plain,(
% 3.07/0.80    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))) )),
% 3.07/0.80    inference(definition_unfolding,[],[f58,f74])).
% 3.07/0.80  fof(f74,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.07/0.80    inference(definition_unfolding,[],[f54,f73])).
% 3.07/0.81  fof(f73,plain,(
% 3.07/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.07/0.81    inference(definition_unfolding,[],[f55,f72])).
% 3.07/0.81  fof(f72,plain,(
% 3.07/0.81    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.07/0.81    inference(definition_unfolding,[],[f67,f71])).
% 3.07/0.81  fof(f71,plain,(
% 3.07/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.07/0.81    inference(definition_unfolding,[],[f69,f70])).
% 3.07/0.81  fof(f70,plain,(
% 3.07/0.81    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.07/0.81    inference(cnf_transformation,[],[f4])).
% 3.07/0.81  fof(f4,axiom,(
% 3.07/0.81    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.07/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 3.07/0.81  fof(f69,plain,(
% 3.07/0.81    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.07/0.81    inference(cnf_transformation,[],[f3])).
% 3.07/0.81  fof(f3,axiom,(
% 3.07/0.81    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.07/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 3.07/0.81  fof(f67,plain,(
% 3.07/0.81    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.07/0.81    inference(cnf_transformation,[],[f2])).
% 3.07/0.81  fof(f2,axiom,(
% 3.07/0.81    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.07/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.07/0.81  fof(f55,plain,(
% 3.07/0.81    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.07/0.81    inference(cnf_transformation,[],[f1])).
% 3.07/0.81  fof(f1,axiom,(
% 3.07/0.81    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.07/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.07/0.81  fof(f54,plain,(
% 3.07/0.81    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.07/0.81    inference(cnf_transformation,[],[f5])).
% 3.07/0.81  fof(f5,axiom,(
% 3.07/0.81    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.07/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.07/0.81  fof(f58,plain,(
% 3.07/0.81    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.07/0.81    inference(cnf_transformation,[],[f31])).
% 3.07/0.81  fof(f31,plain,(
% 3.07/0.81    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.07/0.81    inference(ennf_transformation,[],[f9])).
% 3.07/0.81  fof(f9,axiom,(
% 3.07/0.81    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 3.07/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 3.07/0.81  fof(f77,plain,(
% 3.07/0.81    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k4_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)))) )),
% 3.07/0.81    inference(definition_unfolding,[],[f59,f74])).
% 3.07/0.81  fof(f59,plain,(
% 3.07/0.81    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 3.07/0.81    inference(cnf_transformation,[],[f32])).
% 3.07/0.81  fof(f32,plain,(
% 3.07/0.81    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.07/0.81    inference(ennf_transformation,[],[f13])).
% 3.07/0.81  fof(f13,axiom,(
% 3.07/0.81    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 3.07/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 3.07/0.81  fof(f400,plain,(
% 3.07/0.81    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))),X1) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)))) )),
% 3.07/0.81    inference(superposition,[],[f397,f397])).
% 3.07/0.81  fof(f2814,plain,(
% 3.07/0.81    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 3.07/0.81    inference(unit_resulting_resolution,[],[f474,f301])).
% 3.07/0.81  fof(f301,plain,(
% 3.07/0.81    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 3.07/0.81    inference(forward_demodulation,[],[f98,f226])).
% 3.07/0.81  fof(f98,plain,(
% 3.07/0.81    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 3.07/0.81    inference(forward_demodulation,[],[f97,f49])).
% 3.07/0.81  fof(f97,plain,(
% 3.07/0.81    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 3.07/0.81    inference(resolution,[],[f62,f45])).
% 3.07/0.81  fof(f62,plain,(
% 3.07/0.81    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 3.07/0.81    inference(cnf_transformation,[],[f35])).
% 3.07/0.81  fof(f35,plain,(
% 3.07/0.81    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.07/0.81    inference(flattening,[],[f34])).
% 3.07/0.81  fof(f34,plain,(
% 3.07/0.81    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.07/0.81    inference(ennf_transformation,[],[f11])).
% 3.07/0.81  fof(f11,axiom,(
% 3.07/0.81    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 3.07/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 3.07/0.81  fof(f474,plain,(
% 3.07/0.81    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) )),
% 3.07/0.81    inference(forward_demodulation,[],[f464,f49])).
% 3.07/0.81  fof(f464,plain,(
% 3.07/0.81    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))))) )),
% 3.07/0.81    inference(unit_resulting_resolution,[],[f234,f45,f404,f52])).
% 3.07/0.81  fof(f52,plain,(
% 3.07/0.81    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))) )),
% 3.07/0.81    inference(cnf_transformation,[],[f27])).
% 3.07/0.81  fof(f27,plain,(
% 3.07/0.81    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.07/0.81    inference(flattening,[],[f26])).
% 3.07/0.81  fof(f26,plain,(
% 3.07/0.81    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.07/0.81    inference(ennf_transformation,[],[f15])).
% 3.07/0.81  fof(f15,axiom,(
% 3.07/0.81    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.07/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 3.07/0.81  fof(f404,plain,(
% 3.07/0.81    ( ! [X6,X7] : (r1_tarski(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X7),X6))))) )),
% 3.07/0.81    inference(superposition,[],[f233,f397])).
% 3.07/0.81  fof(f233,plain,(
% 3.07/0.81    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0))) )),
% 3.07/0.81    inference(backward_demodulation,[],[f169,f226])).
% 3.07/0.81  fof(f169,plain,(
% 3.07/0.81    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X0))) )),
% 3.07/0.81    inference(backward_demodulation,[],[f83,f89])).
% 3.07/0.81  fof(f83,plain,(
% 3.07/0.81    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0))) )),
% 3.07/0.81    inference(unit_resulting_resolution,[],[f45,f60])).
% 3.07/0.81  fof(f60,plain,(
% 3.07/0.81    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) )),
% 3.07/0.81    inference(cnf_transformation,[],[f33])).
% 3.07/0.81  fof(f33,plain,(
% 3.07/0.81    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 3.07/0.81    inference(ennf_transformation,[],[f19])).
% 3.07/0.81  fof(f19,axiom,(
% 3.07/0.81    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 3.07/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 3.07/0.81  fof(f234,plain,(
% 3.07/0.81    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 3.07/0.81    inference(backward_demodulation,[],[f172,f226])).
% 3.07/0.81  fof(f172,plain,(
% 3.07/0.81    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 3.07/0.81    inference(backward_demodulation,[],[f103,f89])).
% 3.07/0.81  fof(f103,plain,(
% 3.07/0.81    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 3.07/0.81    inference(unit_resulting_resolution,[],[f45,f87,f53])).
% 3.07/0.81  fof(f53,plain,(
% 3.07/0.81    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.07/0.81    inference(cnf_transformation,[],[f28])).
% 3.07/0.81  fof(f28,plain,(
% 3.07/0.81    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.07/0.81    inference(ennf_transformation,[],[f7])).
% 3.07/0.81  fof(f7,axiom,(
% 3.07/0.81    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.07/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 3.07/0.81  fof(f87,plain,(
% 3.07/0.81    ( ! [X0,X1] : (m1_subset_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k1_zfmisc_1(k6_relat_1(X0)))) )),
% 3.07/0.81    inference(unit_resulting_resolution,[],[f83,f66])).
% 3.07/0.81  fof(f66,plain,(
% 3.07/0.81    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.07/0.81    inference(cnf_transformation,[],[f42])).
% 3.07/0.81  fof(f42,plain,(
% 3.07/0.81    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.07/0.81    inference(nnf_transformation,[],[f6])).
% 3.07/0.81  fof(f6,axiom,(
% 3.07/0.81    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.07/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.07/0.81  fof(f377,plain,(
% 3.07/0.81    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) | spl2_4),
% 3.07/0.81    inference(avatar_component_clause,[],[f375])).
% 3.07/0.81  fof(f375,plain,(
% 3.07/0.81    spl2_4 <=> k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0)))),
% 3.07/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 3.07/0.81  fof(f378,plain,(
% 3.07/0.81    ~spl2_4 | spl2_3),
% 3.07/0.81    inference(avatar_split_clause,[],[f373,f237,f375])).
% 3.07/0.81  fof(f237,plain,(
% 3.07/0.81    spl2_3 <=> k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 3.07/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 3.07/0.81  fof(f373,plain,(
% 3.07/0.81    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) | spl2_3),
% 3.07/0.81    inference(backward_demodulation,[],[f239,f355])).
% 3.07/0.81  fof(f239,plain,(
% 3.07/0.81    k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_3),
% 3.07/0.81    inference(avatar_component_clause,[],[f237])).
% 3.07/0.81  fof(f240,plain,(
% 3.07/0.81    ~spl2_3 | spl2_2),
% 3.07/0.81    inference(avatar_split_clause,[],[f235,f177,f237])).
% 3.07/0.81  fof(f177,plain,(
% 3.07/0.81    spl2_2 <=> k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = k8_relat_1(sK0,k6_relat_1(sK1))),
% 3.07/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.07/0.81  fof(f235,plain,(
% 3.07/0.81    k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_2),
% 3.07/0.81    inference(backward_demodulation,[],[f179,f226])).
% 3.07/0.81  fof(f179,plain,(
% 3.07/0.81    k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) | spl2_2),
% 3.07/0.81    inference(avatar_component_clause,[],[f177])).
% 3.07/0.81  fof(f180,plain,(
% 3.07/0.81    ~spl2_2 | spl2_1),
% 3.07/0.81    inference(avatar_split_clause,[],[f168,f79,f177])).
% 3.07/0.81  fof(f79,plain,(
% 3.07/0.81    spl2_1 <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))),
% 3.07/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.07/0.81  fof(f168,plain,(
% 3.07/0.81    k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) | spl2_1),
% 3.07/0.81    inference(backward_demodulation,[],[f81,f89])).
% 3.07/0.81  fof(f81,plain,(
% 3.07/0.81    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) | spl2_1),
% 3.07/0.81    inference(avatar_component_clause,[],[f79])).
% 3.07/0.81  fof(f82,plain,(
% 3.07/0.81    ~spl2_1),
% 3.07/0.81    inference(avatar_split_clause,[],[f75,f79])).
% 3.07/0.81  fof(f75,plain,(
% 3.07/0.81    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))),
% 3.07/0.81    inference(definition_unfolding,[],[f43,f74])).
% 3.07/0.81  fof(f43,plain,(
% 3.07/0.81    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.07/0.81    inference(cnf_transformation,[],[f41])).
% 3.07/0.81  fof(f41,plain,(
% 3.07/0.81    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.07/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f40])).
% 3.07/0.81  fof(f40,plain,(
% 3.07/0.81    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.07/0.81    introduced(choice_axiom,[])).
% 3.07/0.81  fof(f24,plain,(
% 3.07/0.81    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 3.07/0.81    inference(ennf_transformation,[],[f23])).
% 3.07/0.81  fof(f23,negated_conjecture,(
% 3.07/0.81    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.07/0.81    inference(negated_conjecture,[],[f22])).
% 3.07/0.81  fof(f22,conjecture,(
% 3.07/0.81    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.07/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 3.07/0.81  % SZS output end Proof for theBenchmark
% 3.07/0.81  % (19131)------------------------------
% 3.07/0.81  % (19131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.81  % (19131)Termination reason: Refutation
% 3.07/0.81  
% 3.07/0.81  % (19131)Memory used [KB]: 9466
% 3.07/0.81  % (19131)Time elapsed: 0.349 s
% 3.07/0.81  % (19131)------------------------------
% 3.07/0.81  % (19131)------------------------------
% 3.07/0.82  % (19119)Success in time 0.456 s
%------------------------------------------------------------------------------
