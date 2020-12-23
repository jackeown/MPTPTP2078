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
% DateTime   : Thu Dec  3 12:52:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 525 expanded)
%              Number of leaves         :   17 ( 157 expanded)
%              Depth                    :   25
%              Number of atoms          :  182 ( 801 expanded)
%              Number of equality atoms :   74 ( 378 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4647,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f4407])).

fof(f4407,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(superposition,[],[f86,f3130])).

fof(f3130,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(forward_demodulation,[],[f3129,f68])).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f67,f42])).

fof(f42,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f44,f40])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f3129,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(forward_demodulation,[],[f3125,f398])).

fof(f398,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(resolution,[],[f66,f40])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f60,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f3125,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(resolution,[],[f3122,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f113,f73])).

fof(f73,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f53,f40])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f112,f40])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f57,f43])).

fof(f43,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f3122,plain,(
    ! [X41,X42] : r1_tarski(k1_setfam_1(k2_enumset1(X41,X41,X41,X42)),X41) ),
    inference(forward_demodulation,[],[f3103,f43])).

fof(f3103,plain,(
    ! [X41,X42] : r1_tarski(k2_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X41,X41,X41,X42)))),X41) ),
    inference(superposition,[],[f1097,f910])).

fof(f910,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3),X4) ),
    inference(superposition,[],[f398,f68])).

fof(f1097,plain,(
    ! [X4,X5,X3] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)),X4) ),
    inference(forward_demodulation,[],[f1096,f43])).

fof(f1096,plain,(
    ! [X4,X5,X3] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)),k2_relat_1(k6_relat_1(X4))) ),
    inference(subsumption_resolution,[],[f1095,f934])).

fof(f934,plain,(
    ! [X70,X68,X69] : v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X68),X69),X70)) ),
    inference(superposition,[],[f400,f398])).

fof(f400,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[],[f71,f331])).

fof(f331,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(X1,X0))) ),
    inference(forward_demodulation,[],[f330,f83])).

fof(f83,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f72,f73])).

fof(f72,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f52,f40])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f330,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(X1,X0))) ),
    inference(forward_demodulation,[],[f328,f42])).

fof(f328,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(k6_relat_1(X1)),X0))) ),
    inference(resolution,[],[f65,f40])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f54,f62])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),X1))) ),
    inference(resolution,[],[f64,f40])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f51,f62])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f1095,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)),k2_relat_1(k6_relat_1(X4)))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)) ) ),
    inference(subsumption_resolution,[],[f1084,f40])).

fof(f1084,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)),k2_relat_1(k6_relat_1(X4)))
      | ~ v1_relat_1(k6_relat_1(X4))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)) ) ),
    inference(resolution,[],[f1075,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f1075,plain,(
    ! [X4,X5,X3] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X5),k6_relat_1(X3)) ),
    inference(superposition,[],[f1002,f782])).

fof(f782,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2) ),
    inference(superposition,[],[f767,f671])).

fof(f671,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k8_relat_1(X3,k7_relat_1(k6_relat_1(X2),X3)) ),
    inference(superposition,[],[f407,f451])).

fof(f451,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) ),
    inference(subsumption_resolution,[],[f442,f400])).

fof(f442,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f402,f57])).

fof(f402,plain,(
    ! [X2,X3] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)),X3) ),
    inference(resolution,[],[f400,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))
      | r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) ) ),
    inference(forward_demodulation,[],[f107,f43])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k2_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(subsumption_resolution,[],[f101,f40])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k2_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f47,f84])).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0)) ),
    inference(backward_demodulation,[],[f81,f83])).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X0)) ),
    inference(backward_demodulation,[],[f69,f72])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(resolution,[],[f55,f40])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f407,plain,(
    ! [X14,X15,X13] : k8_relat_1(X13,k7_relat_1(k6_relat_1(X14),X15)) = k5_relat_1(k7_relat_1(k6_relat_1(X14),X15),k6_relat_1(X13)) ),
    inference(resolution,[],[f400,f52])).

fof(f767,plain,(
    ! [X2,X0,X1] : k8_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(backward_demodulation,[],[f334,f408])).

fof(f408,plain,(
    ! [X17,X18,X16] : k5_relat_1(k6_relat_1(X16),k7_relat_1(k6_relat_1(X17),X18)) = k7_relat_1(k7_relat_1(k6_relat_1(X17),X18),X16) ),
    inference(resolution,[],[f400,f53])).

fof(f334,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X0),X2)) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(forward_demodulation,[],[f332,f73])).

fof(f332,plain,(
    ! [X2,X0,X1] : k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X0),X2)) ),
    inference(resolution,[],[f327,f40])).

fof(f327,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(X1,k7_relat_1(k6_relat_1(X0),X2)) ) ),
    inference(forward_demodulation,[],[f325,f83])).

fof(f325,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(X1,k8_relat_1(X0,k6_relat_1(X2)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f58,f40])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(f1002,plain,(
    ! [X4,X2,X5,X3] : r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4),X5),k6_relat_1(X2)) ),
    inference(superposition,[],[f913,f398])).

fof(f913,plain,(
    ! [X6,X7,X5] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X6),X7),k6_relat_1(X5)) ),
    inference(superposition,[],[f85,f398])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f80,f83])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f70,f72])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X1)) ),
    inference(resolution,[],[f56,f40])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f86,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f82,f83])).

fof(f82,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f63,f72])).

fof(f63,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f38,f62])).

fof(f38,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f36])).

fof(f36,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n020.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:34:37 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.19/0.39  % (20774)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.40  % (20782)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.43  % (20772)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.43  % (20776)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.44  % (20770)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.44  % (20771)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.45  % (20777)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.45  % (20783)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.45  % (20778)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.45  % (20773)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.46  % (20779)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.46  % (20786)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.46  % (20785)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.46  % (20787)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.46  % (20781)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.46  % (20781)Refutation not found, incomplete strategy% (20781)------------------------------
% 0.19/0.46  % (20781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (20781)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (20781)Memory used [KB]: 10618
% 0.19/0.46  % (20781)Time elapsed: 0.082 s
% 0.19/0.46  % (20781)------------------------------
% 0.19/0.46  % (20781)------------------------------
% 0.19/0.47  % (20775)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.48  % (20780)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.48  % (20784)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.52  % (20782)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f4647,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(trivial_inequality_removal,[],[f4407])).
% 0.19/0.52  fof(f4407,plain,(
% 0.19/0.52    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.19/0.52    inference(superposition,[],[f86,f3130])).
% 0.19/0.52  fof(f3130,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.19/0.52    inference(forward_demodulation,[],[f3129,f68])).
% 0.19/0.52  fof(f68,plain,(
% 0.19/0.52    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 0.19/0.52    inference(forward_demodulation,[],[f67,f42])).
% 0.19/0.52  fof(f42,plain,(
% 0.19/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f12])).
% 0.19/0.52  fof(f12,axiom,(
% 0.19/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.52  fof(f67,plain,(
% 0.19/0.52    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 0.19/0.52    inference(resolution,[],[f44,f40])).
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f18])).
% 0.19/0.52  fof(f18,axiom,(
% 0.19/0.52    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.19/0.52  fof(f44,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f17])).
% 0.19/0.52  fof(f17,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.19/0.52  fof(f3129,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.19/0.52    inference(forward_demodulation,[],[f3125,f398])).
% 0.19/0.52  fof(f398,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) )),
% 0.19/0.52    inference(resolution,[],[f66,f40])).
% 0.19/0.52  fof(f66,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.19/0.52    inference(definition_unfolding,[],[f60,f62])).
% 0.19/0.52  fof(f62,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.19/0.52    inference(definition_unfolding,[],[f49,f61])).
% 0.19/0.52  fof(f61,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.19/0.52    inference(definition_unfolding,[],[f50,f59])).
% 0.19/0.52  fof(f59,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.52  fof(f50,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.52  fof(f49,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.52  fof(f60,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f35])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.19/0.52    inference(ennf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.19/0.52  fof(f3125,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.19/0.52    inference(resolution,[],[f3122,f114])).
% 0.19/0.52  fof(f114,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 0.19/0.52    inference(forward_demodulation,[],[f113,f73])).
% 0.19/0.52  fof(f73,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 0.19/0.52    inference(resolution,[],[f53,f40])).
% 0.19/0.52  fof(f53,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f16])).
% 0.19/0.52  fof(f16,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.19/0.52  fof(f113,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f112,f40])).
% 0.19/0.52  fof(f112,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.52    inference(superposition,[],[f57,f43])).
% 0.19/0.52  fof(f43,plain,(
% 0.19/0.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f12])).
% 0.19/0.52  fof(f57,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f33])).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f32])).
% 0.19/0.52  fof(f32,plain,(
% 0.19/0.52    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f15])).
% 0.19/0.52  fof(f15,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.19/0.52  fof(f3122,plain,(
% 0.19/0.52    ( ! [X41,X42] : (r1_tarski(k1_setfam_1(k2_enumset1(X41,X41,X41,X42)),X41)) )),
% 0.19/0.52    inference(forward_demodulation,[],[f3103,f43])).
% 0.19/0.52  fof(f3103,plain,(
% 0.19/0.52    ( ! [X41,X42] : (r1_tarski(k2_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X41,X41,X41,X42)))),X41)) )),
% 0.19/0.52    inference(superposition,[],[f1097,f910])).
% 0.19/0.52  fof(f910,plain,(
% 0.19/0.52    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3),X4)) )),
% 0.19/0.52    inference(superposition,[],[f398,f68])).
% 0.19/0.52  fof(f1097,plain,(
% 0.19/0.52    ( ! [X4,X5,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)),X4)) )),
% 0.19/0.52    inference(forward_demodulation,[],[f1096,f43])).
% 0.19/0.52  fof(f1096,plain,(
% 0.19/0.52    ( ! [X4,X5,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)),k2_relat_1(k6_relat_1(X4)))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f1095,f934])).
% 0.19/0.52  fof(f934,plain,(
% 0.19/0.52    ( ! [X70,X68,X69] : (v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X68),X69),X70))) )),
% 0.19/0.52    inference(superposition,[],[f400,f398])).
% 0.19/0.52  fof(f400,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 0.19/0.52    inference(superposition,[],[f71,f331])).
% 0.19/0.52  fof(f331,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(X1,X0)))) )),
% 0.19/0.52    inference(forward_demodulation,[],[f330,f83])).
% 0.19/0.52  fof(f83,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.19/0.52    inference(backward_demodulation,[],[f72,f73])).
% 0.19/0.52  fof(f72,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.19/0.52    inference(resolution,[],[f52,f40])).
% 0.19/0.52  fof(f52,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f28])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f6])).
% 0.19/0.52  fof(f6,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.19/0.52  fof(f330,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(X1,X0)))) )),
% 0.19/0.52    inference(forward_demodulation,[],[f328,f42])).
% 0.19/0.52  fof(f328,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(k6_relat_1(X1)),X0)))) )),
% 0.19/0.52    inference(resolution,[],[f65,f40])).
% 0.19/0.52  fof(f65,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.19/0.52    inference(definition_unfolding,[],[f54,f62])).
% 0.19/0.52  fof(f54,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f30])).
% 0.19/0.52  fof(f30,plain,(
% 0.19/0.52    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).
% 0.19/0.52  fof(f71,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),X1)))) )),
% 0.19/0.52    inference(resolution,[],[f64,f40])).
% 0.19/0.52  fof(f64,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.19/0.52    inference(definition_unfolding,[],[f51,f62])).
% 0.19/0.52  fof(f51,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.19/0.52  fof(f1095,plain,(
% 0.19/0.52    ( ! [X4,X5,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)),k2_relat_1(k6_relat_1(X4))) | ~v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f1084,f40])).
% 0.19/0.52  fof(f1084,plain,(
% 0.19/0.52    ( ! [X4,X5,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)),k2_relat_1(k6_relat_1(X4))) | ~v1_relat_1(k6_relat_1(X4)) | ~v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5))) )),
% 0.19/0.52    inference(resolution,[],[f1075,f47])).
% 0.19/0.52  fof(f47,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f25])).
% 0.19/0.52  fof(f25,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(flattening,[],[f24])).
% 0.19/0.52  fof(f24,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f9])).
% 0.19/0.52  fof(f9,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.19/0.52  fof(f1075,plain,(
% 0.19/0.52    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X5),k6_relat_1(X3))) )),
% 0.19/0.52    inference(superposition,[],[f1002,f782])).
% 0.19/0.52  fof(f782,plain,(
% 0.19/0.52    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2)) )),
% 0.19/0.52    inference(superposition,[],[f767,f671])).
% 0.19/0.52  fof(f671,plain,(
% 0.19/0.52    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k8_relat_1(X3,k7_relat_1(k6_relat_1(X2),X3))) )),
% 0.19/0.52    inference(superposition,[],[f407,f451])).
% 0.19/0.52  fof(f451,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f442,f400])).
% 0.19/0.52  fof(f442,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 0.19/0.52    inference(resolution,[],[f402,f57])).
% 0.19/0.52  fof(f402,plain,(
% 0.19/0.52    ( ! [X2,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)),X3)) )),
% 0.19/0.52    inference(resolution,[],[f400,f108])).
% 0.19/0.52  fof(f108,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) | r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1)) )),
% 0.19/0.52    inference(forward_demodulation,[],[f107,f43])).
% 0.19/0.52  fof(f107,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k2_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f101,f40])).
% 0.19/0.52  fof(f101,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k2_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 0.19/0.52    inference(resolution,[],[f47,f84])).
% 0.19/0.52  fof(f84,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0))) )),
% 0.19/0.52    inference(backward_demodulation,[],[f81,f83])).
% 0.19/0.52  fof(f81,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X0))) )),
% 0.19/0.52    inference(backward_demodulation,[],[f69,f72])).
% 0.19/0.52  fof(f69,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0))) )),
% 0.19/0.52    inference(resolution,[],[f55,f40])).
% 0.19/0.52  fof(f55,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f31])).
% 0.19/0.52  fof(f31,plain,(
% 0.19/0.52    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f14])).
% 0.19/0.52  fof(f14,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 0.19/0.52  fof(f407,plain,(
% 0.19/0.52    ( ! [X14,X15,X13] : (k8_relat_1(X13,k7_relat_1(k6_relat_1(X14),X15)) = k5_relat_1(k7_relat_1(k6_relat_1(X14),X15),k6_relat_1(X13))) )),
% 0.19/0.52    inference(resolution,[],[f400,f52])).
% 0.19/0.52  fof(f767,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k8_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)) )),
% 0.19/0.52    inference(backward_demodulation,[],[f334,f408])).
% 0.19/0.52  fof(f408,plain,(
% 0.19/0.52    ( ! [X17,X18,X16] : (k5_relat_1(k6_relat_1(X16),k7_relat_1(k6_relat_1(X17),X18)) = k7_relat_1(k7_relat_1(k6_relat_1(X17),X18),X16)) )),
% 0.19/0.52    inference(resolution,[],[f400,f53])).
% 0.19/0.52  fof(f334,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X0),X2)) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1))) )),
% 0.19/0.52    inference(forward_demodulation,[],[f332,f73])).
% 0.19/0.52  fof(f332,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X0),X2))) )),
% 0.19/0.52    inference(resolution,[],[f327,f40])).
% 0.19/0.52  fof(f327,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(X1,k7_relat_1(k6_relat_1(X0),X2))) )),
% 0.19/0.52    inference(forward_demodulation,[],[f325,f83])).
% 0.19/0.52  fof(f325,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k8_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(X1,k8_relat_1(X0,k6_relat_1(X2))) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(resolution,[],[f58,f40])).
% 0.19/0.52  fof(f58,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f34])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f8])).
% 0.19/0.52  fof(f8,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).
% 0.19/0.52  fof(f1002,plain,(
% 0.19/0.52    ( ! [X4,X2,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4),X5),k6_relat_1(X2))) )),
% 0.19/0.52    inference(superposition,[],[f913,f398])).
% 0.19/0.52  fof(f913,plain,(
% 0.19/0.52    ( ! [X6,X7,X5] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X6),X7),k6_relat_1(X5))) )),
% 0.19/0.52    inference(superposition,[],[f85,f398])).
% 0.19/0.52  fof(f85,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X1))) )),
% 0.19/0.52    inference(backward_demodulation,[],[f80,f83])).
% 0.19/0.52  fof(f80,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X1))) )),
% 0.19/0.52    inference(backward_demodulation,[],[f70,f72])).
% 0.19/0.52  fof(f70,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X1))) )),
% 0.19/0.52    inference(resolution,[],[f56,f40])).
% 0.19/0.52  fof(f56,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f31])).
% 0.19/0.52  fof(f86,plain,(
% 0.19/0.52    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.19/0.52    inference(backward_demodulation,[],[f82,f83])).
% 0.19/0.52  fof(f82,plain,(
% 0.19/0.52    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 0.19/0.52    inference(backward_demodulation,[],[f63,f72])).
% 0.19/0.52  fof(f63,plain,(
% 0.19/0.52    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.19/0.52    inference(definition_unfolding,[],[f38,f62])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.19/0.52    inference(cnf_transformation,[],[f37])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f36])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f21,plain,(
% 0.19/0.52    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f20])).
% 0.19/0.52  fof(f20,negated_conjecture,(
% 0.19/0.52    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.19/0.52    inference(negated_conjecture,[],[f19])).
% 0.19/0.52  fof(f19,conjecture,(
% 0.19/0.52    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (20782)------------------------------
% 0.19/0.52  % (20782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (20782)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (20782)Memory used [KB]: 4349
% 0.19/0.52  % (20782)Time elapsed: 0.140 s
% 0.19/0.52  % (20782)------------------------------
% 0.19/0.52  % (20782)------------------------------
% 0.19/0.52  % (20769)Success in time 0.19 s
%------------------------------------------------------------------------------
