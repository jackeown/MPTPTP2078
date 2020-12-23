%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 669 expanded)
%              Number of leaves         :   14 ( 207 expanded)
%              Depth                    :   16
%              Number of atoms          :   97 ( 884 expanded)
%              Number of equality atoms :   73 ( 562 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1454,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1444,f1417])).

fof(f1417,plain,(
    ! [X6,X7] : k7_relat_1(k6_relat_1(X6),X7) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X7),X6))) ),
    inference(backward_demodulation,[],[f1126,f1312])).

fof(f1312,plain,(
    ! [X4,X5] : k1_setfam_1(k2_enumset1(X4,X4,X4,X5)) = k1_relat_1(k7_relat_1(k6_relat_1(X5),X4)) ),
    inference(superposition,[],[f45,f1124])).

fof(f1124,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k6_relat_1(X4),X3) ),
    inference(backward_demodulation,[],[f490,f1087])).

fof(f1087,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(superposition,[],[f993,f97])).

fof(f97,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(superposition,[],[f84,f76])).

fof(f76,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f75,f46])).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f75,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) ),
    inference(resolution,[],[f47,f43])).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f47,plain,(
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

fof(f84,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f56,f43])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f993,plain,(
    ! [X4,X5,X3] : k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X5),X4) ),
    inference(superposition,[],[f461,f410])).

fof(f410,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(resolution,[],[f72,f43])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f65,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f461,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) = k7_relat_1(k6_relat_1(X2),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[],[f410,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f51,f66,f66])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f490,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X4) ),
    inference(forward_demodulation,[],[f489,f187])).

fof(f187,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f186,f84])).

fof(f186,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f185,f84])).

fof(f185,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f182,f44])).

fof(f44,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f182,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f181,f43])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f178,f44])).

fof(f178,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f48,f43])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f489,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X3),X4)),X4) ),
    inference(forward_demodulation,[],[f488,f97])).

fof(f488,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X3),X4)),X4) ),
    inference(backward_demodulation,[],[f464,f477])).

fof(f477,plain,(
    ! [X39,X37,X38] : k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X38,X38,X38,X39))),X37) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X37),X38),X39)) ),
    inference(superposition,[],[f187,f410])).

fof(f464,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3),X4) ),
    inference(superposition,[],[f410,f97])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f1126,plain,(
    ! [X6,X7] : k7_relat_1(k6_relat_1(X6),X7) = k6_relat_1(k1_setfam_1(k2_enumset1(X6,X6,X6,X7))) ),
    inference(forward_demodulation,[],[f1125,f1087])).

fof(f1125,plain,(
    ! [X6,X7] : k6_relat_1(k1_setfam_1(k2_enumset1(X6,X6,X6,X7))) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X6) ),
    inference(forward_demodulation,[],[f1123,f187])).

fof(f1123,plain,(
    ! [X6,X7] : k6_relat_1(k1_setfam_1(k2_enumset1(X6,X6,X6,X7))) = k7_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X7),X6)),X6) ),
    inference(backward_demodulation,[],[f1052,f1087])).

fof(f1052,plain,(
    ! [X6,X7] : k6_relat_1(k1_setfam_1(k2_enumset1(X6,X6,X6,X7))) = k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X7),X6),X7)),X6) ),
    inference(forward_demodulation,[],[f994,f477])).

fof(f994,plain,(
    ! [X6,X7] : k6_relat_1(k1_setfam_1(k2_enumset1(X6,X6,X6,X7))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X6,X6,X6,X7))),X7),X6) ),
    inference(superposition,[],[f461,f97])).

fof(f1444,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) ),
    inference(backward_demodulation,[],[f88,f1312])).

fof(f88,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f81,f85])).

fof(f85,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f80,f84])).

fof(f80,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f55,f43])).

fof(f55,plain,(
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

fof(f81,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f68,f80])).

fof(f68,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f42,f67])).

fof(f42,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f40])).

fof(f40,plain,
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
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (4269)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (4270)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (4268)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (4272)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (4266)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (4282)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (4267)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (4278)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (4278)Refutation not found, incomplete strategy% (4278)------------------------------
% 0.20/0.48  % (4278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (4278)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (4278)Memory used [KB]: 10618
% 0.20/0.48  % (4278)Time elapsed: 0.063 s
% 0.20/0.48  % (4278)------------------------------
% 0.20/0.48  % (4278)------------------------------
% 0.20/0.48  % (4273)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (4274)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (4276)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (4279)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (4281)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (4283)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (4275)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (4271)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % (4280)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.52  % (4284)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.57  % (4280)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f1454,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(subsumption_resolution,[],[f1444,f1417])).
% 0.20/0.57  fof(f1417,plain,(
% 0.20/0.57    ( ! [X6,X7] : (k7_relat_1(k6_relat_1(X6),X7) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X7),X6)))) )),
% 0.20/0.57    inference(backward_demodulation,[],[f1126,f1312])).
% 0.20/0.57  fof(f1312,plain,(
% 0.20/0.57    ( ! [X4,X5] : (k1_setfam_1(k2_enumset1(X4,X4,X4,X5)) = k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) )),
% 0.20/0.57    inference(superposition,[],[f45,f1124])).
% 0.20/0.57  fof(f1124,plain,(
% 0.20/0.57    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k6_relat_1(X4),X3)) )),
% 0.20/0.57    inference(backward_demodulation,[],[f490,f1087])).
% 0.20/0.57  fof(f1087,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 0.20/0.57    inference(superposition,[],[f993,f97])).
% 0.20/0.57  fof(f97,plain,(
% 0.20/0.57    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 0.20/0.57    inference(superposition,[],[f84,f76])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 0.20/0.57    inference(forward_demodulation,[],[f75,f46])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,axiom,(
% 0.20/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.57  fof(f75,plain,(
% 0.20/0.57    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) )),
% 0.20/0.57    inference(resolution,[],[f47,f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,axiom,(
% 0.20/0.57    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.20/0.57  fof(f84,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.57    inference(resolution,[],[f56,f43])).
% 0.20/0.58  fof(f56,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f30])).
% 0.20/0.58  fof(f30,plain,(
% 0.20/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f19])).
% 0.20/0.58  fof(f19,axiom,(
% 0.20/0.58    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.58  fof(f993,plain,(
% 0.20/0.58    ( ! [X4,X5,X3] : (k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X5),X4)) )),
% 0.20/0.58    inference(superposition,[],[f461,f410])).
% 0.20/0.58  fof(f410,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) )),
% 0.20/0.58    inference(resolution,[],[f72,f43])).
% 0.20/0.58  fof(f72,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f65,f67])).
% 0.20/0.58  fof(f67,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f53,f66])).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f52,f63])).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.58  fof(f52,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.58  fof(f65,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.58    inference(ennf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.20/0.58  fof(f461,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) = k7_relat_1(k6_relat_1(X2),k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) )),
% 0.20/0.58    inference(superposition,[],[f410,f69])).
% 0.20/0.58  fof(f69,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f51,f66,f66])).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.58  fof(f490,plain,(
% 0.20/0.58    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X4)) )),
% 0.20/0.58    inference(forward_demodulation,[],[f489,f187])).
% 0.20/0.58  fof(f187,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f186,f84])).
% 0.20/0.58  fof(f186,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f185,f84])).
% 0.20/0.58  fof(f185,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f182,f44])).
% 0.20/0.58  fof(f44,plain,(
% 0.20/0.58    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f15])).
% 0.20/0.58  fof(f15,axiom,(
% 0.20/0.58    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 0.20/0.58  fof(f182,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0)))) )),
% 0.20/0.58    inference(resolution,[],[f181,f43])).
% 0.20/0.58  fof(f181,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f178,f44])).
% 0.20/0.58  fof(f178,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(resolution,[],[f48,f43])).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f25])).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f13])).
% 0.20/0.58  fof(f13,axiom,(
% 0.20/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.20/0.58  fof(f489,plain,(
% 0.20/0.58    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X3),X4)),X4)) )),
% 0.20/0.58    inference(forward_demodulation,[],[f488,f97])).
% 0.20/0.58  fof(f488,plain,(
% 0.20/0.58    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X3),X4)),X4)) )),
% 0.20/0.58    inference(backward_demodulation,[],[f464,f477])).
% 0.20/0.58  fof(f477,plain,(
% 0.20/0.58    ( ! [X39,X37,X38] : (k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X38,X38,X38,X39))),X37) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X37),X38),X39))) )),
% 0.20/0.58    inference(superposition,[],[f187,f410])).
% 0.20/0.58  fof(f464,plain,(
% 0.20/0.58    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3),X4)) )),
% 0.20/0.58    inference(superposition,[],[f410,f97])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f14])).
% 0.20/0.58  fof(f1126,plain,(
% 0.20/0.58    ( ! [X6,X7] : (k7_relat_1(k6_relat_1(X6),X7) = k6_relat_1(k1_setfam_1(k2_enumset1(X6,X6,X6,X7)))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f1125,f1087])).
% 0.20/0.58  fof(f1125,plain,(
% 0.20/0.58    ( ! [X6,X7] : (k6_relat_1(k1_setfam_1(k2_enumset1(X6,X6,X6,X7))) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X6)) )),
% 0.20/0.58    inference(forward_demodulation,[],[f1123,f187])).
% 0.20/0.58  fof(f1123,plain,(
% 0.20/0.58    ( ! [X6,X7] : (k6_relat_1(k1_setfam_1(k2_enumset1(X6,X6,X6,X7))) = k7_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X7),X6)),X6)) )),
% 0.20/0.58    inference(backward_demodulation,[],[f1052,f1087])).
% 0.20/0.58  fof(f1052,plain,(
% 0.20/0.58    ( ! [X6,X7] : (k6_relat_1(k1_setfam_1(k2_enumset1(X6,X6,X6,X7))) = k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X7),X6),X7)),X6)) )),
% 0.20/0.58    inference(forward_demodulation,[],[f994,f477])).
% 0.20/0.58  fof(f994,plain,(
% 0.20/0.58    ( ! [X6,X7] : (k6_relat_1(k1_setfam_1(k2_enumset1(X6,X6,X6,X7))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X6,X6,X6,X7))),X7),X6)) )),
% 0.20/0.58    inference(superposition,[],[f461,f97])).
% 0.20/0.58  fof(f1444,plain,(
% 0.20/0.58    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK1),sK0)))),
% 0.20/0.58    inference(backward_demodulation,[],[f88,f1312])).
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.58    inference(backward_demodulation,[],[f81,f85])).
% 0.20/0.58  fof(f85,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.58    inference(backward_demodulation,[],[f80,f84])).
% 0.20/0.58  fof(f80,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.20/0.58    inference(resolution,[],[f55,f43])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f29])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.58  fof(f81,plain,(
% 0.20/0.58    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 0.20/0.58    inference(backward_demodulation,[],[f68,f80])).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.20/0.58    inference(definition_unfolding,[],[f42,f67])).
% 0.20/0.58  fof(f42,plain,(
% 0.20/0.58    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.58    inference(cnf_transformation,[],[f41])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f22])).
% 0.20/0.58  fof(f22,negated_conjecture,(
% 0.20/0.58    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.58    inference(negated_conjecture,[],[f21])).
% 0.20/0.58  fof(f21,conjecture,(
% 0.20/0.58    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (4280)------------------------------
% 0.20/0.58  % (4280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (4280)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (4280)Memory used [KB]: 3070
% 0.20/0.58  % (4280)Time elapsed: 0.161 s
% 0.20/0.58  % (4280)------------------------------
% 0.20/0.58  % (4280)------------------------------
% 0.20/0.58  % (4260)Success in time 0.222 s
%------------------------------------------------------------------------------
