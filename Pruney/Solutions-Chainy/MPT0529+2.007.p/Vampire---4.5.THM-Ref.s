%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:58 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 179 expanded)
%              Number of leaves         :   14 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :   93 ( 284 expanded)
%              Number of equality atoms :   55 ( 178 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(subsumption_resolution,[],[f176,f62])).

fof(f62,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    inference(superposition,[],[f25,f56])).

fof(f56,plain,(
    ! [X2,X3] : k8_relat_1(X2,k8_relat_1(X3,sK2)) = k8_relat_1(X3,k8_relat_1(X2,sK2)) ),
    inference(superposition,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),sK2) ),
    inference(resolution,[],[f46,f23])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

fof(f52,plain,(
    ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)),sK2) ),
    inference(superposition,[],[f50,f44])).

fof(f44,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f29,f42,f42])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f25,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f176,plain,(
    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    inference(forward_demodulation,[],[f169,f28])).

fof(f28,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f169,plain,(
    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(k2_relat_1(k6_relat_1(sK0)),sK2) ),
    inference(superposition,[],[f155,f49])).

fof(f49,plain,(
    k6_relat_1(sK0) = k8_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(resolution,[],[f48,f24])).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f47,f26])).

fof(f26,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f33,f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f155,plain,(
    ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),sK2) ),
    inference(backward_demodulation,[],[f50,f152])).

fof(f152,plain,(
    ! [X2,X1] : k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))) = k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)) ),
    inference(forward_demodulation,[],[f151,f28])).

fof(f151,plain,(
    ! [X2,X1] : k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))) = k1_setfam_1(k5_enumset1(k2_relat_1(k6_relat_1(X2)),k2_relat_1(k6_relat_1(X2)),k2_relat_1(k6_relat_1(X2)),k2_relat_1(k6_relat_1(X2)),k2_relat_1(k6_relat_1(X2)),k2_relat_1(k6_relat_1(X2)),X1)) ),
    inference(resolution,[],[f45,f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k5_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f32,f43])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : run_vampire %s %d
% 0.16/0.37  % Computer   : n024.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % WCLimit    : 600
% 0.16/0.37  % DateTime   : Tue Dec  1 10:14:21 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.24/0.44  % (9285)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.24/0.49  % (9274)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.24/0.49  % (9272)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.24/0.49  % (9271)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.24/0.49  % (9269)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.24/0.50  % (9281)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.24/0.51  % (9280)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.24/0.51  % (9277)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.24/0.51  % (9282)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.24/0.51  % (9278)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.24/0.51  % (9273)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.24/0.52  % (9276)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.24/0.52  % (9278)Refutation found. Thanks to Tanya!
% 0.24/0.52  % SZS status Theorem for theBenchmark
% 0.24/0.52  % SZS output start Proof for theBenchmark
% 0.24/0.52  fof(f177,plain,(
% 0.24/0.52    $false),
% 0.24/0.52    inference(subsumption_resolution,[],[f176,f62])).
% 0.24/0.52  fof(f62,plain,(
% 0.24/0.52    k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))),
% 0.24/0.52    inference(superposition,[],[f25,f56])).
% 0.24/0.52  fof(f56,plain,(
% 0.24/0.52    ( ! [X2,X3] : (k8_relat_1(X2,k8_relat_1(X3,sK2)) = k8_relat_1(X3,k8_relat_1(X2,sK2))) )),
% 0.24/0.52    inference(superposition,[],[f52,f50])).
% 0.24/0.52  fof(f50,plain,(
% 0.24/0.52    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),sK2)) )),
% 0.24/0.52    inference(resolution,[],[f46,f23])).
% 0.24/0.52  fof(f23,plain,(
% 0.24/0.52    v1_relat_1(sK2)),
% 0.24/0.52    inference(cnf_transformation,[],[f22])).
% 0.24/0.52  fof(f22,plain,(
% 0.24/0.52    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f21])).
% 0.24/0.52  fof(f21,plain,(
% 0.24/0.52    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.24/0.52    introduced(choice_axiom,[])).
% 0.24/0.52  fof(f16,plain,(
% 0.24/0.52    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.24/0.52    inference(flattening,[],[f15])).
% 0.24/0.52  fof(f15,plain,(
% 0.24/0.52    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.24/0.52    inference(ennf_transformation,[],[f14])).
% 0.24/0.52  fof(f14,negated_conjecture,(
% 0.24/0.52    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.24/0.52    inference(negated_conjecture,[],[f13])).
% 0.24/0.52  fof(f13,conjecture,(
% 0.24/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 0.24/0.52  fof(f46,plain,(
% 0.24/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X2)) )),
% 0.24/0.52    inference(definition_unfolding,[],[f35,f43])).
% 0.24/0.52  fof(f43,plain,(
% 0.24/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.24/0.52    inference(definition_unfolding,[],[f31,f42])).
% 0.24/0.52  fof(f42,plain,(
% 0.24/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.24/0.52    inference(definition_unfolding,[],[f30,f41])).
% 0.24/0.52  fof(f41,plain,(
% 0.24/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.24/0.52    inference(definition_unfolding,[],[f34,f40])).
% 0.24/0.52  fof(f40,plain,(
% 0.24/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.24/0.52    inference(definition_unfolding,[],[f36,f39])).
% 0.24/0.52  fof(f39,plain,(
% 0.24/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.24/0.52    inference(definition_unfolding,[],[f37,f38])).
% 0.24/0.52  fof(f38,plain,(
% 0.24/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.24/0.52    inference(cnf_transformation,[],[f6])).
% 0.24/0.52  fof(f6,axiom,(
% 0.24/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.24/0.52  fof(f37,plain,(
% 0.24/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.24/0.52    inference(cnf_transformation,[],[f5])).
% 0.24/0.52  fof(f5,axiom,(
% 0.24/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.24/0.52  fof(f36,plain,(
% 0.24/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.24/0.52    inference(cnf_transformation,[],[f4])).
% 0.24/0.52  fof(f4,axiom,(
% 0.24/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.24/0.52  fof(f34,plain,(
% 0.24/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.24/0.52    inference(cnf_transformation,[],[f3])).
% 0.24/0.52  fof(f3,axiom,(
% 0.24/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.24/0.52  fof(f30,plain,(
% 0.24/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.24/0.52    inference(cnf_transformation,[],[f2])).
% 0.24/0.52  fof(f2,axiom,(
% 0.24/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.24/0.52  fof(f31,plain,(
% 0.24/0.52    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.24/0.52    inference(cnf_transformation,[],[f7])).
% 0.24/0.52  fof(f7,axiom,(
% 0.24/0.52    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.24/0.52  fof(f35,plain,(
% 0.24/0.52    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.24/0.52    inference(cnf_transformation,[],[f20])).
% 0.24/0.52  fof(f20,plain,(
% 0.24/0.52    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.24/0.52    inference(ennf_transformation,[],[f11])).
% 0.24/0.52  fof(f11,axiom,(
% 0.24/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 0.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).
% 0.24/0.52  fof(f52,plain,(
% 0.24/0.52    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)),sK2)) )),
% 0.24/0.52    inference(superposition,[],[f50,f44])).
% 0.24/0.52  fof(f44,plain,(
% 0.24/0.52    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) )),
% 0.24/0.52    inference(definition_unfolding,[],[f29,f42,f42])).
% 0.24/0.52  fof(f29,plain,(
% 0.24/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.24/0.52    inference(cnf_transformation,[],[f1])).
% 0.24/0.52  fof(f1,axiom,(
% 0.24/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.24/0.52  fof(f25,plain,(
% 0.24/0.52    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.24/0.52    inference(cnf_transformation,[],[f22])).
% 0.24/0.52  fof(f176,plain,(
% 0.24/0.52    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))),
% 0.24/0.52    inference(forward_demodulation,[],[f169,f28])).
% 0.24/0.52  fof(f28,plain,(
% 0.24/0.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.24/0.52    inference(cnf_transformation,[],[f12])).
% 0.24/0.52  fof(f12,axiom,(
% 0.24/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.24/0.52  fof(f169,plain,(
% 0.24/0.52    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(k2_relat_1(k6_relat_1(sK0)),sK2)),
% 0.24/0.52    inference(superposition,[],[f155,f49])).
% 0.24/0.52  fof(f49,plain,(
% 0.24/0.52    k6_relat_1(sK0) = k8_relat_1(sK1,k6_relat_1(sK0))),
% 0.24/0.52    inference(resolution,[],[f48,f24])).
% 0.24/0.52  fof(f24,plain,(
% 0.24/0.52    r1_tarski(sK0,sK1)),
% 0.24/0.52    inference(cnf_transformation,[],[f22])).
% 0.24/0.52  fof(f48,plain,(
% 0.24/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 0.24/0.52    inference(subsumption_resolution,[],[f47,f26])).
% 0.24/0.52  fof(f26,plain,(
% 0.24/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.24/0.52    inference(cnf_transformation,[],[f8])).
% 0.24/0.52  fof(f8,axiom,(
% 0.24/0.52    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.24/0.52  fof(f47,plain,(
% 0.24/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.24/0.52    inference(superposition,[],[f33,f28])).
% 0.24/0.52  fof(f33,plain,(
% 0.24/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 0.24/0.52    inference(cnf_transformation,[],[f19])).
% 0.24/0.52  fof(f19,plain,(
% 0.24/0.52    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.24/0.52    inference(flattening,[],[f18])).
% 0.24/0.52  fof(f18,plain,(
% 0.24/0.52    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.24/0.52    inference(ennf_transformation,[],[f10])).
% 0.24/0.52  fof(f10,axiom,(
% 0.24/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.24/0.52  fof(f155,plain,(
% 0.24/0.52    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),sK2)) )),
% 0.24/0.52    inference(backward_demodulation,[],[f50,f152])).
% 0.24/0.52  fof(f152,plain,(
% 0.24/0.52    ( ! [X2,X1] : (k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))) = k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) )),
% 0.24/0.52    inference(forward_demodulation,[],[f151,f28])).
% 0.24/0.52  fof(f151,plain,(
% 0.24/0.52    ( ! [X2,X1] : (k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))) = k1_setfam_1(k5_enumset1(k2_relat_1(k6_relat_1(X2)),k2_relat_1(k6_relat_1(X2)),k2_relat_1(k6_relat_1(X2)),k2_relat_1(k6_relat_1(X2)),k2_relat_1(k6_relat_1(X2)),k2_relat_1(k6_relat_1(X2)),X1))) )),
% 0.24/0.52    inference(resolution,[],[f45,f26])).
% 0.24/0.52  fof(f45,plain,(
% 0.24/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k5_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))) )),
% 0.24/0.52    inference(definition_unfolding,[],[f32,f43])).
% 0.24/0.52  fof(f32,plain,(
% 0.24/0.52    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.24/0.52    inference(cnf_transformation,[],[f17])).
% 0.24/0.52  fof(f17,plain,(
% 0.24/0.52    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.24/0.52    inference(ennf_transformation,[],[f9])).
% 0.24/0.52  fof(f9,axiom,(
% 0.24/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 0.24/0.52  % SZS output end Proof for theBenchmark
% 0.24/0.52  % (9278)------------------------------
% 0.24/0.52  % (9278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.52  % (9278)Termination reason: Refutation
% 0.24/0.52  
% 0.24/0.52  % (9278)Memory used [KB]: 10746
% 0.24/0.52  % (9278)Time elapsed: 0.086 s
% 0.24/0.52  % (9278)------------------------------
% 0.24/0.52  % (9278)------------------------------
% 0.24/0.52  % (9286)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.24/0.52  % (9275)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.24/0.52  % (9283)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.24/0.53  % (9268)Success in time 0.144 s
%------------------------------------------------------------------------------
