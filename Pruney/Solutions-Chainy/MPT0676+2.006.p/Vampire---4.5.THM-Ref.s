%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  81 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 178 expanded)
%              Number of equality atoms :   28 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(resolution,[],[f160,f23])).

fof(f23,plain,(
    ~ r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

% (5076)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_funct_1)).

fof(f160,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k8_relat_1(X1,sK2),X0),k9_relat_1(sK2,X0)) ),
    inference(superposition,[],[f24,f146])).

fof(f146,plain,(
    ! [X0,X1] : k9_relat_1(k8_relat_1(X0,sK2),X1) = k4_xboole_0(k9_relat_1(sK2,X1),k4_xboole_0(k9_relat_1(sK2,X1),X0)) ),
    inference(forward_demodulation,[],[f145,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1)) = k9_relat_1(k8_relat_1(X0,sK2),X1) ),
    inference(resolution,[],[f39,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X5)
      | k2_relat_1(k7_relat_1(k8_relat_1(X4,X5),X6)) = k9_relat_1(k8_relat_1(X4,X5),X6) ) ),
    inference(resolution,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f145,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1)) = k4_xboole_0(k9_relat_1(sK2,X1),k4_xboole_0(k9_relat_1(sK2,X1),X0)) ),
    inference(forward_demodulation,[],[f144,f40])).

fof(f40,plain,(
    ! [X0,X1] : k7_relat_1(k8_relat_1(X0,sK2),X1) = k8_relat_1(X0,k7_relat_1(sK2,X1)) ),
    inference(resolution,[],[f32,f21])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f144,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k4_xboole_0(k9_relat_1(sK2,X1),k4_xboole_0(k9_relat_1(sK2,X1),X0)) ),
    inference(forward_demodulation,[],[f137,f37])).

fof(f37,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f30,f21])).

fof(f137,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k4_xboole_0(k2_relat_1(k7_relat_1(sK2,X1)),k4_xboole_0(k2_relat_1(k7_relat_1(sK2,X1)),X0)) ),
    inference(resolution,[],[f47,f21])).

fof(f47,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X2)
      | k2_relat_1(k8_relat_1(X1,k7_relat_1(X2,X3))) = k4_xboole_0(k2_relat_1(k7_relat_1(X2,X3)),k4_xboole_0(k2_relat_1(k7_relat_1(X2,X3)),X1)) ) ),
    inference(resolution,[],[f36,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(forward_demodulation,[],[f35,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (5085)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (5075)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (5074)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (5082)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (5089)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (5090)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (5081)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (5080)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (5078)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (5088)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (5087)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (5075)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (5083)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (5086)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(resolution,[],[f160,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ~r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ~r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  % (5076)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)))),
% 0.20/0.50    inference(negated_conjecture,[],[f10])).
% 0.20/0.50  fof(f10,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_funct_1)).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k8_relat_1(X1,sK2),X0),k9_relat_1(sK2,X0))) )),
% 0.20/0.50    inference(superposition,[],[f24,f146])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k9_relat_1(k8_relat_1(X0,sK2),X1) = k4_xboole_0(k9_relat_1(sK2,X1),k4_xboole_0(k9_relat_1(sK2,X1),X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f145,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1)) = k9_relat_1(k8_relat_1(X0,sK2),X1)) )),
% 0.20/0.50    inference(resolution,[],[f39,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    v1_relat_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X6,X4,X5] : (~v1_relat_1(X5) | k2_relat_1(k7_relat_1(k8_relat_1(X4,X5),X6)) = k9_relat_1(k8_relat_1(X4,X5),X6)) )),
% 0.20/0.50    inference(resolution,[],[f30,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1)) = k4_xboole_0(k9_relat_1(sK2,X1),k4_xboole_0(k9_relat_1(sK2,X1),X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f144,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,sK2),X1) = k8_relat_1(X0,k7_relat_1(sK2,X1))) )),
% 0.20/0.50    inference(resolution,[],[f32,f21])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k4_xboole_0(k9_relat_1(sK2,X1),k4_xboole_0(k9_relat_1(sK2,X1),X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f137,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 0.20/0.50    inference(resolution,[],[f30,f21])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k4_xboole_0(k2_relat_1(k7_relat_1(sK2,X1)),k4_xboole_0(k2_relat_1(k7_relat_1(sK2,X1)),X0))) )),
% 0.20/0.50    inference(resolution,[],[f47,f21])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X2,X3,X1] : (~v1_relat_1(X2) | k2_relat_1(k8_relat_1(X1,k7_relat_1(X2,X3))) = k4_xboole_0(k2_relat_1(k7_relat_1(X2,X3)),k4_xboole_0(k2_relat_1(k7_relat_1(X2,X3)),X1))) )),
% 0.20/0.50    inference(resolution,[],[f36,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f35,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f27,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f25,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f31,f33])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (5075)------------------------------
% 0.20/0.50  % (5075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (5075)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (5075)Memory used [KB]: 1791
% 0.20/0.50  % (5075)Time elapsed: 0.064 s
% 0.20/0.50  % (5075)------------------------------
% 0.20/0.50  % (5075)------------------------------
% 0.20/0.50  % (5073)Success in time 0.14 s
%------------------------------------------------------------------------------
