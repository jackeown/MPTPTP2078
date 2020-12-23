%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:29 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  106 (1180 expanded)
%              Number of leaves         :   19 ( 352 expanded)
%              Depth                    :   20
%              Number of atoms          :  190 (1923 expanded)
%              Number of equality atoms :   80 ( 860 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1599,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1598,f1508])).

fof(f1508,plain,(
    ! [X10,X11] : k7_relat_1(k6_relat_1(X10),X11) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X10),X11))) ),
    inference(backward_demodulation,[],[f194,f1507])).

fof(f1507,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3) ),
    inference(forward_demodulation,[],[f1494,f191])).

fof(f191,plain,(
    ! [X4,X3] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4))),X3) ),
    inference(resolution,[],[f104,f100])).

fof(f100,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X1) ),
    inference(forward_demodulation,[],[f98,f91])).

fof(f91,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f98,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))),X1) ),
    inference(resolution,[],[f97,f42])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))),X1) ) ),
    inference(forward_demodulation,[],[f95,f45])).

fof(f45,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))),k2_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f48,f42])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f103,f91])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f101,f44])).

fof(f44,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(resolution,[],[f59,f42])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f1494,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),X3) ),
    inference(superposition,[],[f121,f118])).

fof(f118,plain,(
    ! [X6,X7,X5] : k5_relat_1(k7_relat_1(k6_relat_1(X5),X7),k6_relat_1(X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7) ),
    inference(subsumption_resolution,[],[f117,f42])).

fof(f117,plain,(
    ! [X6,X7,X5] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(X5),X7),k6_relat_1(X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7)
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(subsumption_resolution,[],[f113,f42])).

fof(f113,plain,(
    ! [X6,X7,X5] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(X5),X7),k6_relat_1(X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7)
      | ~ v1_relat_1(k6_relat_1(X6))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(superposition,[],[f60,f91])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

% (29414)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(f121,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
    inference(resolution,[],[f120,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f120,plain,(
    ! [X8,X9] : v1_relat_1(k7_relat_1(k6_relat_1(X9),X8)) ),
    inference(subsumption_resolution,[],[f119,f42])).

fof(f119,plain,(
    ! [X8,X9] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X9),X8))
      | ~ v1_relat_1(k6_relat_1(X8)) ) ),
    inference(subsumption_resolution,[],[f114,f42])).

fof(f114,plain,(
    ! [X8,X9] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X9),X8))
      | ~ v1_relat_1(k6_relat_1(X9))
      | ~ v1_relat_1(k6_relat_1(X8)) ) ),
    inference(superposition,[],[f61,f91])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f194,plain,(
    ! [X10,X11] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X10),X11))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X10),X11))),X11) ),
    inference(resolution,[],[f104,f153])).

fof(f153,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X0) ),
    inference(backward_demodulation,[],[f135,f152])).

fof(f152,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f151,f93])).

fof(f93,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f88,f91])).

fof(f88,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f53,f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f151,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f148,f45])).

fof(f148,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X1))),X0)) ),
    inference(resolution,[],[f136,f42])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(X1)),X0)) ) ),
    inference(backward_demodulation,[],[f71,f133])).

fof(f133,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(subsumption_resolution,[],[f131,f42])).

fof(f131,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f70,f44])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f55,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f56,f67])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f135,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    inference(backward_demodulation,[],[f69,f133])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f50,f67])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1598,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(backward_demodulation,[],[f160,f1592])).

fof(f1592,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(subsumption_resolution,[],[f1591,f1558])).

fof(f1558,plain,(
    ! [X173,X172] : r1_tarski(k7_relat_1(k6_relat_1(X172),X173),k7_relat_1(k6_relat_1(X173),X172)) ),
    inference(backward_demodulation,[],[f1311,f1508])).

fof(f1311,plain,(
    ! [X173,X172] : r1_tarski(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X172),X173))),k7_relat_1(k6_relat_1(X173),X172)) ),
    inference(superposition,[],[f510,f191])).

fof(f510,plain,(
    ! [X50,X51,X49] : r1_tarski(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X49),X50))),X51),k7_relat_1(k6_relat_1(X50),X51)) ),
    inference(superposition,[],[f257,f194])).

fof(f257,plain,(
    ! [X6,X7,X5] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),X6),k7_relat_1(k6_relat_1(X5),X6)) ),
    inference(subsumption_resolution,[],[f252,f120])).

fof(f252,plain,(
    ! [X6,X7,X5] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),X6),k7_relat_1(k6_relat_1(X5),X6))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X5),X6)) ) ),
    inference(superposition,[],[f57,f118])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f1591,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k7_relat_1(k6_relat_1(X3),X2))
      | k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) ) ),
    inference(forward_demodulation,[],[f1564,f1508])).

fof(f1564,plain,(
    ! [X2,X3] :
      ( k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X2)))) ) ),
    inference(backward_demodulation,[],[f1393,f1508])).

fof(f1393,plain,(
    ! [X2,X3] :
      ( k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X2)))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X2)))) ) ),
    inference(resolution,[],[f1311,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f160,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) ),
    inference(backward_demodulation,[],[f138,f152])).

fof(f138,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(backward_demodulation,[],[f94,f133])).

fof(f94,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f90,f93])).

fof(f90,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f68,f88])).

fof(f68,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f41,f67])).

fof(f41,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f37])).

fof(f37,plain,
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.22/0.51  % (29377)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.22/0.51  % (29382)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.22/0.51  % (29373)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.22/0.52  % (29383)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.22/0.52  % (29385)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.22/0.52  % (29380)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.31/0.53  % (29393)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.31/0.53  % (29385)Refutation not found, incomplete strategy% (29385)------------------------------
% 1.31/0.53  % (29385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (29385)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (29385)Memory used [KB]: 10618
% 1.31/0.53  % (29385)Time elapsed: 0.111 s
% 1.31/0.53  % (29385)------------------------------
% 1.31/0.53  % (29385)------------------------------
% 1.31/0.53  % (29396)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.31/0.53  % (29374)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.31/0.53  % (29374)Refutation not found, incomplete strategy% (29374)------------------------------
% 1.31/0.53  % (29374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (29374)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (29374)Memory used [KB]: 1663
% 1.31/0.53  % (29374)Time elapsed: 0.114 s
% 1.31/0.53  % (29374)------------------------------
% 1.31/0.53  % (29374)------------------------------
% 1.31/0.53  % (29387)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.31/0.53  % (29387)Refutation not found, incomplete strategy% (29387)------------------------------
% 1.31/0.53  % (29387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (29378)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.31/0.53  % (29401)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.31/0.53  % (29401)Refutation not found, incomplete strategy% (29401)------------------------------
% 1.31/0.53  % (29401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (29401)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (29401)Memory used [KB]: 10746
% 1.31/0.53  % (29401)Time elapsed: 0.125 s
% 1.31/0.53  % (29401)------------------------------
% 1.31/0.53  % (29401)------------------------------
% 1.31/0.53  % (29375)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.31/0.54  % (29376)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.31/0.54  % (29381)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.31/0.54  % (29383)Refutation not found, incomplete strategy% (29383)------------------------------
% 1.31/0.54  % (29383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (29383)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (29383)Memory used [KB]: 10618
% 1.31/0.54  % (29383)Time elapsed: 0.126 s
% 1.31/0.54  % (29383)------------------------------
% 1.31/0.54  % (29383)------------------------------
% 1.31/0.54  % (29394)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.31/0.54  % (29379)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.54  % (29400)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.31/0.54  % (29399)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.31/0.54  % (29400)Refutation not found, incomplete strategy% (29400)------------------------------
% 1.31/0.54  % (29400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (29400)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (29400)Memory used [KB]: 6140
% 1.31/0.54  % (29400)Time elapsed: 0.139 s
% 1.31/0.54  % (29400)------------------------------
% 1.31/0.54  % (29400)------------------------------
% 1.31/0.54  % (29399)Refutation not found, incomplete strategy% (29399)------------------------------
% 1.31/0.54  % (29399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (29399)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (29399)Memory used [KB]: 6140
% 1.31/0.54  % (29399)Time elapsed: 0.140 s
% 1.31/0.54  % (29399)------------------------------
% 1.31/0.54  % (29399)------------------------------
% 1.31/0.54  % (29392)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.31/0.54  % (29395)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.31/0.55  % (29398)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.31/0.55  % (29398)Refutation not found, incomplete strategy% (29398)------------------------------
% 1.31/0.55  % (29398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (29386)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.31/0.55  % (29402)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.31/0.55  % (29402)Refutation not found, incomplete strategy% (29402)------------------------------
% 1.31/0.55  % (29402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (29402)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (29402)Memory used [KB]: 1663
% 1.31/0.55  % (29402)Time elapsed: 0.138 s
% 1.31/0.55  % (29402)------------------------------
% 1.31/0.55  % (29402)------------------------------
% 1.31/0.55  % (29384)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.31/0.55  % (29398)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (29398)Memory used [KB]: 6140
% 1.31/0.55  % (29398)Time elapsed: 0.133 s
% 1.31/0.55  % (29398)------------------------------
% 1.31/0.55  % (29398)------------------------------
% 1.31/0.55  % (29391)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.31/0.55  % (29384)Refutation not found, incomplete strategy% (29384)------------------------------
% 1.31/0.55  % (29384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (29384)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (29384)Memory used [KB]: 6140
% 1.31/0.55  % (29384)Time elapsed: 0.151 s
% 1.31/0.55  % (29384)------------------------------
% 1.31/0.55  % (29384)------------------------------
% 1.31/0.55  % (29391)Refutation not found, incomplete strategy% (29391)------------------------------
% 1.31/0.55  % (29391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (29391)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (29391)Memory used [KB]: 1663
% 1.31/0.55  % (29391)Time elapsed: 0.149 s
% 1.31/0.55  % (29391)------------------------------
% 1.31/0.55  % (29391)------------------------------
% 1.31/0.55  % (29387)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (29387)Memory used [KB]: 1663
% 1.31/0.55  % (29387)Time elapsed: 0.088 s
% 1.31/0.55  % (29387)------------------------------
% 1.31/0.55  % (29387)------------------------------
% 1.31/0.55  % (29397)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.31/0.55  % (29397)Refutation not found, incomplete strategy% (29397)------------------------------
% 1.31/0.55  % (29397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (29397)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (29397)Memory used [KB]: 10618
% 1.31/0.55  % (29397)Time elapsed: 0.137 s
% 1.31/0.55  % (29397)------------------------------
% 1.31/0.55  % (29397)------------------------------
% 1.31/0.55  % (29390)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.31/0.55  % (29388)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.31/0.55  % (29390)Refutation not found, incomplete strategy% (29390)------------------------------
% 1.31/0.55  % (29390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (29390)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (29390)Memory used [KB]: 1663
% 1.31/0.55  % (29390)Time elapsed: 0.149 s
% 1.31/0.55  % (29390)------------------------------
% 1.31/0.55  % (29390)------------------------------
% 1.31/0.56  % (29389)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.31/0.56  % (29389)Refutation not found, incomplete strategy% (29389)------------------------------
% 1.31/0.56  % (29389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (29389)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (29389)Memory used [KB]: 10618
% 1.31/0.56  % (29389)Time elapsed: 0.147 s
% 1.31/0.56  % (29389)------------------------------
% 1.31/0.56  % (29389)------------------------------
% 1.92/0.65  % (29408)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.92/0.66  % (29376)Refutation not found, incomplete strategy% (29376)------------------------------
% 1.92/0.66  % (29376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.66  % (29376)Termination reason: Refutation not found, incomplete strategy
% 1.92/0.66  
% 1.92/0.66  % (29376)Memory used [KB]: 6140
% 1.92/0.66  % (29376)Time elapsed: 0.256 s
% 1.92/0.66  % (29376)------------------------------
% 1.92/0.66  % (29376)------------------------------
% 1.92/0.67  % (29375)Refutation not found, incomplete strategy% (29375)------------------------------
% 1.92/0.67  % (29375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.67  % (29375)Termination reason: Refutation not found, incomplete strategy
% 1.92/0.67  
% 1.92/0.67  % (29375)Memory used [KB]: 6140
% 1.92/0.67  % (29375)Time elapsed: 0.256 s
% 1.92/0.67  % (29375)------------------------------
% 1.92/0.67  % (29375)------------------------------
% 1.92/0.67  % (29410)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.92/0.67  % (29412)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 1.92/0.67  % (29411)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.92/0.67  % (29412)Refutation not found, incomplete strategy% (29412)------------------------------
% 1.92/0.67  % (29412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.67  % (29412)Termination reason: Refutation not found, incomplete strategy
% 1.92/0.67  
% 1.92/0.67  % (29412)Memory used [KB]: 10618
% 1.92/0.67  % (29412)Time elapsed: 0.094 s
% 1.92/0.67  % (29412)------------------------------
% 1.92/0.67  % (29412)------------------------------
% 1.92/0.67  % (29411)Refutation not found, incomplete strategy% (29411)------------------------------
% 1.92/0.67  % (29411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.67  % (29411)Termination reason: Refutation not found, incomplete strategy
% 1.92/0.67  
% 1.92/0.67  % (29411)Memory used [KB]: 10618
% 1.92/0.67  % (29411)Time elapsed: 0.096 s
% 1.92/0.67  % (29411)------------------------------
% 1.92/0.67  % (29411)------------------------------
% 1.92/0.67  % (29409)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.92/0.67  % (29381)Refutation not found, incomplete strategy% (29381)------------------------------
% 1.92/0.67  % (29381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.67  % (29381)Termination reason: Refutation not found, incomplete strategy
% 1.92/0.67  
% 1.92/0.67  % (29381)Memory used [KB]: 6268
% 1.92/0.67  % (29381)Time elapsed: 0.255 s
% 1.92/0.67  % (29381)------------------------------
% 1.92/0.67  % (29381)------------------------------
% 1.92/0.67  % (29413)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 1.92/0.67  % (29413)Refutation not found, incomplete strategy% (29413)------------------------------
% 1.92/0.67  % (29413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.67  % (29413)Termination reason: Refutation not found, incomplete strategy
% 1.92/0.67  
% 1.92/0.67  % (29413)Memory used [KB]: 1663
% 1.92/0.67  % (29413)Time elapsed: 0.104 s
% 1.92/0.67  % (29413)------------------------------
% 1.92/0.67  % (29413)------------------------------
% 1.92/0.68  % (29395)Refutation found. Thanks to Tanya!
% 1.92/0.68  % SZS status Theorem for theBenchmark
% 1.92/0.68  % SZS output start Proof for theBenchmark
% 1.92/0.68  fof(f1599,plain,(
% 1.92/0.68    $false),
% 1.92/0.68    inference(subsumption_resolution,[],[f1598,f1508])).
% 1.92/0.68  fof(f1508,plain,(
% 1.92/0.68    ( ! [X10,X11] : (k7_relat_1(k6_relat_1(X10),X11) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X10),X11)))) )),
% 1.92/0.68    inference(backward_demodulation,[],[f194,f1507])).
% 1.92/0.68  fof(f1507,plain,(
% 1.92/0.68    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)) )),
% 1.92/0.68    inference(forward_demodulation,[],[f1494,f191])).
% 1.92/0.68  fof(f191,plain,(
% 1.92/0.68    ( ! [X4,X3] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4))),X3)) )),
% 1.92/0.68    inference(resolution,[],[f104,f100])).
% 1.92/0.68  fof(f100,plain,(
% 1.92/0.68    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X1)) )),
% 1.92/0.68    inference(forward_demodulation,[],[f98,f91])).
% 1.92/0.68  fof(f91,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.92/0.68    inference(resolution,[],[f54,f42])).
% 1.92/0.68  fof(f42,plain,(
% 1.92/0.68    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.92/0.68    inference(cnf_transformation,[],[f19])).
% 1.92/0.68  fof(f19,axiom,(
% 1.92/0.68    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.92/0.68  fof(f54,plain,(
% 1.92/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.92/0.68    inference(cnf_transformation,[],[f28])).
% 1.92/0.68  fof(f28,plain,(
% 1.92/0.68    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.92/0.68    inference(ennf_transformation,[],[f18])).
% 1.92/0.68  fof(f18,axiom,(
% 1.92/0.68    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.92/0.68  fof(f98,plain,(
% 1.92/0.68    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))),X1)) )),
% 1.92/0.68    inference(resolution,[],[f97,f42])).
% 1.92/0.68  fof(f97,plain,(
% 1.92/0.68    ( ! [X0,X1] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))),X1)) )),
% 1.92/0.68    inference(forward_demodulation,[],[f95,f45])).
% 1.92/0.68  fof(f45,plain,(
% 1.92/0.68    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.92/0.68    inference(cnf_transformation,[],[f12])).
% 1.92/0.68  fof(f12,axiom,(
% 1.92/0.68    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.92/0.68  fof(f95,plain,(
% 1.92/0.68    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))),k2_relat_1(k6_relat_1(X1))) | ~v1_relat_1(X0)) )),
% 1.92/0.68    inference(resolution,[],[f48,f42])).
% 1.92/0.68  fof(f48,plain,(
% 1.92/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.92/0.68    inference(cnf_transformation,[],[f25])).
% 1.92/0.68  fof(f25,plain,(
% 1.92/0.68    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.92/0.68    inference(ennf_transformation,[],[f10])).
% 1.92/0.68  fof(f10,axiom,(
% 1.92/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.92/0.68  fof(f104,plain,(
% 1.92/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.92/0.68    inference(forward_demodulation,[],[f103,f91])).
% 1.92/0.68  fof(f103,plain,(
% 1.92/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 1.92/0.68    inference(forward_demodulation,[],[f101,f44])).
% 1.92/0.68  fof(f44,plain,(
% 1.92/0.68    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.92/0.68    inference(cnf_transformation,[],[f12])).
% 1.92/0.68  fof(f101,plain,(
% 1.92/0.68    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 1.92/0.68    inference(resolution,[],[f59,f42])).
% 1.92/0.68  fof(f59,plain,(
% 1.92/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 1.92/0.68    inference(cnf_transformation,[],[f33])).
% 1.92/0.68  fof(f33,plain,(
% 1.92/0.68    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.92/0.68    inference(flattening,[],[f32])).
% 1.92/0.68  fof(f32,plain,(
% 1.92/0.68    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.92/0.68    inference(ennf_transformation,[],[f14])).
% 1.92/0.68  fof(f14,axiom,(
% 1.92/0.68    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 1.92/0.68  fof(f1494,plain,(
% 1.92/0.68    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),X3)) )),
% 1.92/0.68    inference(superposition,[],[f121,f118])).
% 1.92/0.68  fof(f118,plain,(
% 1.92/0.68    ( ! [X6,X7,X5] : (k5_relat_1(k7_relat_1(k6_relat_1(X5),X7),k6_relat_1(X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7)) )),
% 1.92/0.68    inference(subsumption_resolution,[],[f117,f42])).
% 1.92/0.68  fof(f117,plain,(
% 1.92/0.68    ( ! [X6,X7,X5] : (k5_relat_1(k7_relat_1(k6_relat_1(X5),X7),k6_relat_1(X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7) | ~v1_relat_1(k6_relat_1(X5))) )),
% 1.92/0.68    inference(subsumption_resolution,[],[f113,f42])).
% 1.92/0.68  fof(f113,plain,(
% 1.92/0.68    ( ! [X6,X7,X5] : (k5_relat_1(k7_relat_1(k6_relat_1(X5),X7),k6_relat_1(X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(k6_relat_1(X5))) )),
% 1.92/0.68    inference(superposition,[],[f60,f91])).
% 1.92/0.68  fof(f60,plain,(
% 1.92/0.68    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.92/0.68    inference(cnf_transformation,[],[f34])).
% 1.92/0.68  % (29414)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 1.92/0.68  fof(f34,plain,(
% 1.92/0.68    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.92/0.68    inference(ennf_transformation,[],[f7])).
% 1.92/0.68  fof(f7,axiom,(
% 1.92/0.68    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).
% 1.92/0.68  fof(f121,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) )),
% 1.92/0.68    inference(resolution,[],[f120,f46])).
% 1.92/0.68  fof(f46,plain,(
% 1.92/0.68    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.92/0.68    inference(cnf_transformation,[],[f23])).
% 1.92/0.68  fof(f23,plain,(
% 1.92/0.68    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.92/0.68    inference(ennf_transformation,[],[f16])).
% 1.92/0.68  fof(f16,axiom,(
% 1.92/0.68    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.92/0.68  fof(f120,plain,(
% 1.92/0.68    ( ! [X8,X9] : (v1_relat_1(k7_relat_1(k6_relat_1(X9),X8))) )),
% 1.92/0.68    inference(subsumption_resolution,[],[f119,f42])).
% 1.92/0.68  fof(f119,plain,(
% 1.92/0.68    ( ! [X8,X9] : (v1_relat_1(k7_relat_1(k6_relat_1(X9),X8)) | ~v1_relat_1(k6_relat_1(X8))) )),
% 1.92/0.68    inference(subsumption_resolution,[],[f114,f42])).
% 1.92/0.68  fof(f114,plain,(
% 1.92/0.68    ( ! [X8,X9] : (v1_relat_1(k7_relat_1(k6_relat_1(X9),X8)) | ~v1_relat_1(k6_relat_1(X9)) | ~v1_relat_1(k6_relat_1(X8))) )),
% 1.92/0.68    inference(superposition,[],[f61,f91])).
% 1.92/0.68  fof(f61,plain,(
% 1.92/0.68    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.92/0.68    inference(cnf_transformation,[],[f36])).
% 1.92/0.68  fof(f36,plain,(
% 1.92/0.68    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.92/0.68    inference(flattening,[],[f35])).
% 1.92/0.68  fof(f35,plain,(
% 1.92/0.68    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.92/0.68    inference(ennf_transformation,[],[f6])).
% 1.92/0.68  fof(f6,axiom,(
% 1.92/0.68    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.92/0.68  fof(f194,plain,(
% 1.92/0.68    ( ! [X10,X11] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X10),X11))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X10),X11))),X11)) )),
% 1.92/0.68    inference(resolution,[],[f104,f153])).
% 1.92/0.68  fof(f153,plain,(
% 1.92/0.68    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X0)) )),
% 1.92/0.68    inference(backward_demodulation,[],[f135,f152])).
% 1.92/0.68  fof(f152,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.92/0.68    inference(forward_demodulation,[],[f151,f93])).
% 1.92/0.68  fof(f93,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.92/0.68    inference(backward_demodulation,[],[f88,f91])).
% 1.92/0.68  fof(f88,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 1.92/0.68    inference(resolution,[],[f53,f42])).
% 1.92/0.68  fof(f53,plain,(
% 1.92/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 1.92/0.68    inference(cnf_transformation,[],[f27])).
% 1.92/0.68  fof(f27,plain,(
% 1.92/0.68    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.92/0.68    inference(ennf_transformation,[],[f9])).
% 1.92/0.68  fof(f9,axiom,(
% 1.92/0.68    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 1.92/0.68  fof(f151,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.92/0.68    inference(forward_demodulation,[],[f148,f45])).
% 1.92/0.68  fof(f148,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X1))),X0))) )),
% 1.92/0.68    inference(resolution,[],[f136,f42])).
% 1.92/0.68  fof(f136,plain,(
% 1.92/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(X1)),X0))) )),
% 1.92/0.68    inference(backward_demodulation,[],[f71,f133])).
% 1.92/0.68  fof(f133,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.92/0.68    inference(subsumption_resolution,[],[f131,f42])).
% 1.92/0.68  fof(f131,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.92/0.68    inference(superposition,[],[f70,f44])).
% 1.92/0.68  fof(f70,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.92/0.68    inference(definition_unfolding,[],[f55,f67])).
% 1.92/0.68  fof(f67,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.92/0.68    inference(definition_unfolding,[],[f51,f66])).
% 1.92/0.68  fof(f66,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.92/0.68    inference(definition_unfolding,[],[f52,f65])).
% 1.92/0.68  fof(f65,plain,(
% 1.92/0.68    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.92/0.68    inference(cnf_transformation,[],[f4])).
% 1.92/0.68  fof(f4,axiom,(
% 1.92/0.68    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.92/0.68  fof(f52,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.92/0.68    inference(cnf_transformation,[],[f3])).
% 1.92/0.68  fof(f3,axiom,(
% 1.92/0.68    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.92/0.68  fof(f51,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.92/0.68    inference(cnf_transformation,[],[f5])).
% 1.92/0.68  fof(f5,axiom,(
% 1.92/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.92/0.68  fof(f55,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.92/0.68    inference(cnf_transformation,[],[f29])).
% 1.92/0.68  fof(f29,plain,(
% 1.92/0.68    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.92/0.68    inference(ennf_transformation,[],[f17])).
% 1.92/0.68  fof(f17,axiom,(
% 1.92/0.68    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.92/0.68  fof(f71,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.92/0.68    inference(definition_unfolding,[],[f56,f67])).
% 1.92/0.68  fof(f56,plain,(
% 1.92/0.68    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.92/0.68    inference(cnf_transformation,[],[f30])).
% 1.92/0.68  fof(f30,plain,(
% 1.92/0.68    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.92/0.68    inference(ennf_transformation,[],[f8])).
% 1.92/0.68  fof(f8,axiom,(
% 1.92/0.68    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 1.92/0.68  fof(f135,plain,(
% 1.92/0.68    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) )),
% 1.92/0.68    inference(backward_demodulation,[],[f69,f133])).
% 1.92/0.68  fof(f69,plain,(
% 1.92/0.68    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 1.92/0.68    inference(definition_unfolding,[],[f50,f67])).
% 1.92/0.68  fof(f50,plain,(
% 1.92/0.68    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.92/0.68    inference(cnf_transformation,[],[f2])).
% 1.92/0.68  fof(f2,axiom,(
% 1.92/0.68    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.92/0.68  fof(f1598,plain,(
% 1.92/0.68    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 1.92/0.68    inference(backward_demodulation,[],[f160,f1592])).
% 1.92/0.68  fof(f1592,plain,(
% 1.92/0.68    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 1.92/0.68    inference(subsumption_resolution,[],[f1591,f1558])).
% 1.92/0.68  fof(f1558,plain,(
% 1.92/0.68    ( ! [X173,X172] : (r1_tarski(k7_relat_1(k6_relat_1(X172),X173),k7_relat_1(k6_relat_1(X173),X172))) )),
% 1.92/0.68    inference(backward_demodulation,[],[f1311,f1508])).
% 1.92/0.68  fof(f1311,plain,(
% 1.92/0.68    ( ! [X173,X172] : (r1_tarski(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X172),X173))),k7_relat_1(k6_relat_1(X173),X172))) )),
% 1.92/0.68    inference(superposition,[],[f510,f191])).
% 1.92/0.68  fof(f510,plain,(
% 1.92/0.68    ( ! [X50,X51,X49] : (r1_tarski(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X49),X50))),X51),k7_relat_1(k6_relat_1(X50),X51))) )),
% 1.92/0.68    inference(superposition,[],[f257,f194])).
% 1.92/0.68  fof(f257,plain,(
% 1.92/0.68    ( ! [X6,X7,X5] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),X6),k7_relat_1(k6_relat_1(X5),X6))) )),
% 1.92/0.68    inference(subsumption_resolution,[],[f252,f120])).
% 1.92/0.68  fof(f252,plain,(
% 1.92/0.68    ( ! [X6,X7,X5] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),X6),k7_relat_1(k6_relat_1(X5),X6)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) )),
% 1.92/0.68    inference(superposition,[],[f57,f118])).
% 1.92/0.68  fof(f57,plain,(
% 1.92/0.68    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 1.92/0.68    inference(cnf_transformation,[],[f31])).
% 1.92/0.68  fof(f31,plain,(
% 1.92/0.68    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.92/0.68    inference(ennf_transformation,[],[f13])).
% 1.92/0.68  fof(f13,axiom,(
% 1.92/0.68    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 1.92/0.68  fof(f1591,plain,(
% 1.92/0.68    ( ! [X2,X3] : (~r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k7_relat_1(k6_relat_1(X3),X2)) | k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 1.92/0.68    inference(forward_demodulation,[],[f1564,f1508])).
% 1.92/0.68  fof(f1564,plain,(
% 1.92/0.68    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) | ~r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X2))))) )),
% 1.92/0.68    inference(backward_demodulation,[],[f1393,f1508])).
% 1.92/0.68  fof(f1393,plain,(
% 1.92/0.68    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X2))) | ~r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X2))))) )),
% 1.92/0.68    inference(resolution,[],[f1311,f64])).
% 1.92/0.68  fof(f64,plain,(
% 1.92/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.92/0.68    inference(cnf_transformation,[],[f40])).
% 1.92/0.68  fof(f40,plain,(
% 1.92/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.92/0.68    inference(flattening,[],[f39])).
% 1.92/0.68  fof(f39,plain,(
% 1.92/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.92/0.68    inference(nnf_transformation,[],[f1])).
% 1.92/0.68  fof(f1,axiom,(
% 1.92/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.92/0.68  fof(f160,plain,(
% 1.92/0.68    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0)))),
% 1.92/0.68    inference(backward_demodulation,[],[f138,f152])).
% 1.92/0.68  fof(f138,plain,(
% 1.92/0.68    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 1.92/0.68    inference(backward_demodulation,[],[f94,f133])).
% 1.92/0.68  fof(f94,plain,(
% 1.92/0.68    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.92/0.68    inference(backward_demodulation,[],[f90,f93])).
% 1.92/0.68  fof(f90,plain,(
% 1.92/0.68    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 1.92/0.68    inference(backward_demodulation,[],[f68,f88])).
% 1.92/0.68  fof(f68,plain,(
% 1.92/0.68    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.92/0.68    inference(definition_unfolding,[],[f41,f67])).
% 1.92/0.68  fof(f41,plain,(
% 1.92/0.68    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.92/0.68    inference(cnf_transformation,[],[f38])).
% 1.92/0.68  fof(f38,plain,(
% 1.92/0.68    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.92/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f37])).
% 1.92/0.68  fof(f37,plain,(
% 1.92/0.68    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.92/0.68    introduced(choice_axiom,[])).
% 1.92/0.68  fof(f22,plain,(
% 1.92/0.68    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.92/0.68    inference(ennf_transformation,[],[f21])).
% 1.92/0.68  fof(f21,negated_conjecture,(
% 1.92/0.68    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.92/0.68    inference(negated_conjecture,[],[f20])).
% 1.92/0.68  fof(f20,conjecture,(
% 1.92/0.68    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.92/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.92/0.68  % SZS output end Proof for theBenchmark
% 1.92/0.68  % (29395)------------------------------
% 1.92/0.68  % (29395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.68  % (29395)Termination reason: Refutation
% 1.92/0.68  
% 1.92/0.68  % (29395)Memory used [KB]: 7803
% 1.92/0.68  % (29395)Time elapsed: 0.231 s
% 1.92/0.68  % (29395)------------------------------
% 1.92/0.68  % (29395)------------------------------
% 1.92/0.68  % (29416)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 1.92/0.68  % (29370)Success in time 0.311 s
%------------------------------------------------------------------------------
