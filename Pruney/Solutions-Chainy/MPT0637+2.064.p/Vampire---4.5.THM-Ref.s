%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  127 (3624 expanded)
%              Number of leaves         :   21 (1072 expanded)
%              Depth                    :   24
%              Number of atoms          :  193 (5586 expanded)
%              Number of equality atoms :  117 (2481 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1250,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1202,f1102])).

fof(f1102,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(superposition,[],[f1080,f115])).

fof(f115,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f114,f82])).

fof(f82,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f114,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f113,f82])).

fof(f113,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f110,f39])).

fof(f39,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f110,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f109,f38])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f106,f39])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f45,f38])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f1080,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X4),X3) = k4_relat_1(k7_relat_1(k6_relat_1(X4),X3)) ),
    inference(superposition,[],[f175,f1009])).

fof(f1009,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X3) ),
    inference(backward_demodulation,[],[f214,f1008])).

fof(f1008,plain,(
    ! [X6,X5] : k7_relat_1(k6_relat_1(X5),X6) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X5))),X6) ),
    inference(forward_demodulation,[],[f951,f378])).

fof(f378,plain,(
    ! [X0,X1] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))),X0) ),
    inference(backward_demodulation,[],[f98,f376])).

fof(f376,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f375,f118])).

fof(f118,plain,(
    ! [X8,X7] : k2_relat_1(k7_relat_1(k6_relat_1(X7),X8)) = k1_relat_1(k7_relat_1(k6_relat_1(X8),X7)) ),
    inference(backward_demodulation,[],[f93,f115])).

fof(f93,plain,(
    ! [X8,X7] : k2_relat_1(k7_relat_1(k6_relat_1(X7),X8)) = k1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X7),X8))) ),
    inference(resolution,[],[f89,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f89,plain,(
    ! [X2,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(subsumption_resolution,[],[f88,f38])).

fof(f88,plain,(
    ! [X2,X1] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f87,f38])).

fof(f87,plain,(
    ! [X2,X1] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f54,f82])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f375,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f370,f40])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f370,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(resolution,[],[f68,f38])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f98,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(resolution,[],[f67,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f96,f82])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f95,f38])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f52,f40])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f951,plain,(
    ! [X6,X5] : k7_relat_1(k6_relat_1(X5),X6) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X5))),X5),X6) ),
    inference(superposition,[],[f214,f903])).

fof(f903,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(backward_demodulation,[],[f533,f890])).

fof(f890,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(resolution,[],[f122,f379])).

fof(f379,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X0) ),
    inference(backward_demodulation,[],[f67,f376])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2)
      | k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ) ),
    inference(forward_demodulation,[],[f121,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f89,f50])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k6_relat_1(X1),X0) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0))
      | ~ r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2) ) ),
    inference(forward_demodulation,[],[f120,f115])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2)
      | k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) ),
    inference(subsumption_resolution,[],[f117,f89])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))
      | ~ r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2)
      | k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) ),
    inference(backward_demodulation,[],[f103,f115])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2)
      | k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)))
      | ~ v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) ),
    inference(superposition,[],[f52,f93])).

fof(f533,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) ),
    inference(forward_demodulation,[],[f517,f41])).

fof(f41,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f517,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) = k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) ),
    inference(superposition,[],[f409,f439])).

fof(f439,plain,(
    ! [X8,X9] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X8),X9))) = k7_relat_1(k6_relat_1(X9),k2_relat_1(k7_relat_1(k6_relat_1(X8),X9))) ),
    inference(forward_demodulation,[],[f420,f39])).

fof(f420,plain,(
    ! [X8,X9] : k7_relat_1(k6_relat_1(X9),k2_relat_1(k7_relat_1(k6_relat_1(X8),X9))) = k4_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X8),X9)))) ),
    inference(superposition,[],[f115,f378])).

fof(f409,plain,(
    ! [X6,X7,X5] : k2_relat_1(k7_relat_1(k6_relat_1(X7),k2_relat_1(k7_relat_1(k6_relat_1(X6),X5)))) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X7),X6),X5)) ),
    inference(forward_demodulation,[],[f408,f178])).

fof(f178,plain,(
    ! [X6,X7,X5] : k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)) ),
    inference(backward_demodulation,[],[f148,f175])).

fof(f148,plain,(
    ! [X6,X7,X5] : k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k1_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))) ),
    inference(forward_demodulation,[],[f145,f90])).

fof(f145,plain,(
    ! [X6,X7,X5] : k2_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k1_relat_1(k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7)))) ),
    inference(resolution,[],[f134,f89])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k1_relat_1(k4_relat_1(k5_relat_1(k6_relat_1(X1),X0))) ) ),
    inference(resolution,[],[f76,f38])).

fof(f76,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | k2_relat_1(k5_relat_1(X3,X2)) = k1_relat_1(k4_relat_1(k5_relat_1(X3,X2))) ) ),
    inference(resolution,[],[f54,f43])).

fof(f408,plain,(
    ! [X6,X7,X5] : k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X5),X6),X7)) = k2_relat_1(k7_relat_1(k6_relat_1(X7),k2_relat_1(k7_relat_1(k6_relat_1(X6),X5)))) ),
    inference(forward_demodulation,[],[f404,f118])).

fof(f404,plain,(
    ! [X6,X7,X5] : k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X5),X6),X7)) = k2_relat_1(k7_relat_1(k6_relat_1(X7),k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)))) ),
    inference(resolution,[],[f377,f89])).

fof(f377,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(X1))) ) ),
    inference(backward_demodulation,[],[f68,f376])).

fof(f214,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),X3) ),
    inference(superposition,[],[f91,f174])).

fof(f174,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
    inference(forward_demodulation,[],[f170,f82])).

fof(f170,plain,(
    ! [X2,X0,X1] : k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f166,f38])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f53,f38])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f91,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)))) ),
    inference(resolution,[],[f89,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f175,plain,(
    ! [X6,X7,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),X6)) ),
    inference(backward_demodulation,[],[f124,f174])).

fof(f124,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7) ),
    inference(forward_demodulation,[],[f123,f90])).

fof(f123,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k5_relat_1(k6_relat_1(X7),k7_relat_1(k6_relat_1(X6),X5)) ),
    inference(forward_demodulation,[],[f112,f115])).

fof(f112,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k5_relat_1(k6_relat_1(X7),k4_relat_1(k7_relat_1(k6_relat_1(X5),X6))) ),
    inference(resolution,[],[f109,f89])).

fof(f1202,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(superposition,[],[f904,f1010])).

fof(f1010,plain,(
    ! [X10,X9] : k7_relat_1(k6_relat_1(X9),X10) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X10),X9))) ),
    inference(forward_demodulation,[],[f953,f1008])).

fof(f953,plain,(
    ! [X10,X9] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X10),X9))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X10),X9))),X10) ),
    inference(superposition,[],[f378,f903])).

fof(f904,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(backward_demodulation,[],[f380,f903])).

fof(f380,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) ),
    inference(backward_demodulation,[],[f84,f376])).

fof(f84,plain,(
    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f66,f82])).

fof(f66,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f37,f65])).

fof(f37,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f35])).

fof(f35,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (28874)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (28866)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (28861)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (28868)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (28862)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (28867)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (28863)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (28860)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (28873)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (28859)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (28869)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (28870)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (28871)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (28872)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (28864)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (28865)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (28870)Refutation not found, incomplete strategy% (28870)------------------------------
% 0.21/0.50  % (28870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28870)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (28870)Memory used [KB]: 10618
% 0.21/0.50  % (28870)Time elapsed: 0.082 s
% 0.21/0.50  % (28870)------------------------------
% 0.21/0.50  % (28870)------------------------------
% 0.21/0.50  % (28875)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (28876)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (28868)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f1250,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f1202,f1102])).
% 0.21/0.52  fof(f1102,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 0.21/0.52    inference(superposition,[],[f1080,f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f114,f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.52    inference(resolution,[],[f50,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f113,f82])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f110,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0)))) )),
% 0.21/0.53    inference(resolution,[],[f109,f38])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f106,f39])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(resolution,[],[f45,f38])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.21/0.53  fof(f1080,plain,(
% 0.21/0.53    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X4),X3) = k4_relat_1(k7_relat_1(k6_relat_1(X4),X3))) )),
% 0.21/0.53    inference(superposition,[],[f175,f1009])).
% 0.21/0.53  fof(f1009,plain,(
% 0.21/0.53    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X3)) )),
% 0.21/0.53    inference(backward_demodulation,[],[f214,f1008])).
% 0.21/0.53  fof(f1008,plain,(
% 0.21/0.53    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X5),X6) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X5))),X6)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f951,f378])).
% 0.21/0.53  fof(f378,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))),X0)) )),
% 0.21/0.53    inference(backward_demodulation,[],[f98,f376])).
% 0.21/0.53  fof(f376,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f375,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ( ! [X8,X7] : (k2_relat_1(k7_relat_1(k6_relat_1(X7),X8)) = k1_relat_1(k7_relat_1(k6_relat_1(X8),X7))) )),
% 0.21/0.53    inference(backward_demodulation,[],[f93,f115])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X8,X7] : (k2_relat_1(k7_relat_1(k6_relat_1(X7),X8)) = k1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X7),X8)))) )),
% 0.21/0.53    inference(resolution,[],[f89,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f88,f38])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f87,f38])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.21/0.53    inference(superposition,[],[f54,f82])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.53  fof(f375,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f370,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.53  fof(f370,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1))) )),
% 0.21/0.53    inference(resolution,[],[f68,f38])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f51,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f48,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f49,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f55,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f56,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f57,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f58,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 0.21/0.53    inference(resolution,[],[f67,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f96,f82])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f95,f38])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.53    inference(superposition,[],[f52,f40])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f47,f65])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.53  fof(f951,plain,(
% 0.21/0.53    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X5),X6) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X5))),X5),X6)) )),
% 0.21/0.53    inference(superposition,[],[f214,f903])).
% 0.21/0.53  fof(f903,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 0.21/0.53    inference(backward_demodulation,[],[f533,f890])).
% 0.21/0.53  fof(f890,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 0.21/0.53    inference(resolution,[],[f122,f379])).
% 0.21/0.53  fof(f379,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X0)) )),
% 0.21/0.53    inference(backward_demodulation,[],[f67,f376])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2) | k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f121,f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) )),
% 0.21/0.53    inference(resolution,[],[f89,f50])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0)) | ~r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f120,f115])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2) | k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f117,f89])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) | ~r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2) | k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 0.21/0.53    inference(backward_demodulation,[],[f103,f115])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2) | k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) | ~v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 0.21/0.53    inference(superposition,[],[f52,f93])).
% 0.21/0.53  fof(f533,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f517,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f517,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) = k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))))) )),
% 0.21/0.53    inference(superposition,[],[f409,f439])).
% 0.21/0.53  fof(f439,plain,(
% 0.21/0.53    ( ! [X8,X9] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X8),X9))) = k7_relat_1(k6_relat_1(X9),k2_relat_1(k7_relat_1(k6_relat_1(X8),X9)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f420,f39])).
% 0.21/0.53  fof(f420,plain,(
% 0.21/0.53    ( ! [X8,X9] : (k7_relat_1(k6_relat_1(X9),k2_relat_1(k7_relat_1(k6_relat_1(X8),X9))) = k4_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X8),X9))))) )),
% 0.21/0.53    inference(superposition,[],[f115,f378])).
% 0.21/0.53  fof(f409,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (k2_relat_1(k7_relat_1(k6_relat_1(X7),k2_relat_1(k7_relat_1(k6_relat_1(X6),X5)))) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X7),X6),X5))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f408,f178])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6))) )),
% 0.21/0.53    inference(backward_demodulation,[],[f148,f175])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k1_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f145,f90])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (k2_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k1_relat_1(k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))))) )),
% 0.21/0.53    inference(resolution,[],[f134,f89])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k1_relat_1(k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)))) )),
% 0.21/0.53    inference(resolution,[],[f76,f38])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~v1_relat_1(X3) | ~v1_relat_1(X2) | k2_relat_1(k5_relat_1(X3,X2)) = k1_relat_1(k4_relat_1(k5_relat_1(X3,X2)))) )),
% 0.21/0.53    inference(resolution,[],[f54,f43])).
% 0.21/0.53  fof(f408,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X5),X6),X7)) = k2_relat_1(k7_relat_1(k6_relat_1(X7),k2_relat_1(k7_relat_1(k6_relat_1(X6),X5))))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f404,f118])).
% 0.21/0.53  fof(f404,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X5),X6),X7)) = k2_relat_1(k7_relat_1(k6_relat_1(X7),k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))))) )),
% 0.21/0.53    inference(resolution,[],[f377,f89])).
% 0.21/0.53  fof(f377,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(X1)))) )),
% 0.21/0.53    inference(backward_demodulation,[],[f68,f376])).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),X3)) )),
% 0.21/0.53    inference(superposition,[],[f91,f174])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f170,f82])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))) )),
% 0.21/0.53    inference(resolution,[],[f166,f38])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k7_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1))) )),
% 0.21/0.53    inference(resolution,[],[f53,f38])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4))))) )),
% 0.21/0.53    inference(resolution,[],[f89,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),X6))) )),
% 0.21/0.53    inference(backward_demodulation,[],[f124,f174])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f123,f90])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k5_relat_1(k6_relat_1(X7),k7_relat_1(k6_relat_1(X6),X5))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f112,f115])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k5_relat_1(k6_relat_1(X7),k4_relat_1(k7_relat_1(k6_relat_1(X5),X6)))) )),
% 0.21/0.53    inference(resolution,[],[f109,f89])).
% 0.21/0.53  fof(f1202,plain,(
% 0.21/0.53    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0)),
% 0.21/0.53    inference(superposition,[],[f904,f1010])).
% 0.21/0.53  fof(f1010,plain,(
% 0.21/0.53    ( ! [X10,X9] : (k7_relat_1(k6_relat_1(X9),X10) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X10),X9)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f953,f1008])).
% 0.21/0.53  fof(f953,plain,(
% 0.21/0.53    ( ! [X10,X9] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X10),X9))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X10),X9))),X10)) )),
% 0.21/0.53    inference(superposition,[],[f378,f903])).
% 0.21/0.53  fof(f904,plain,(
% 0.21/0.53    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 0.21/0.53    inference(backward_demodulation,[],[f380,f903])).
% 0.21/0.53  fof(f380,plain,(
% 0.21/0.53    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0)))),
% 0.21/0.53    inference(backward_demodulation,[],[f84,f376])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.53    inference(backward_demodulation,[],[f66,f82])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 0.21/0.53    inference(definition_unfolding,[],[f37,f65])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.53    inference(negated_conjecture,[],[f21])).
% 0.21/0.53  fof(f21,conjecture,(
% 0.21/0.53    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (28868)------------------------------
% 0.21/0.53  % (28868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28868)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (28868)Memory used [KB]: 11641
% 0.21/0.53  % (28868)Time elapsed: 0.106 s
% 0.21/0.53  % (28868)------------------------------
% 0.21/0.53  % (28868)------------------------------
% 0.21/0.53  % (28858)Success in time 0.171 s
%------------------------------------------------------------------------------
