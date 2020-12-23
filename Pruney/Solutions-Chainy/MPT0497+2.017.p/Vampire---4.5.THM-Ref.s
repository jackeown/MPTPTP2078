%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 188 expanded)
%              Number of leaves         :   10 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 380 expanded)
%              Number of equality atoms :   45 ( 171 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(subsumption_resolution,[],[f199,f188])).

fof(f188,plain,(
    ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f187])).

fof(f187,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f20,f186])).

fof(f186,plain,(
    k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f185,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f47,f19])).

fof(f19,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f47,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) ) ),
    inference(superposition,[],[f39,f45])).

fof(f45,plain,
    ( k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),sK0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[],[f41,f19])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,X1)) ) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f37,plain,(
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

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f185,plain,
    ( r2_hidden(sK2(k7_relat_1(sK1,sK0)),k1_xboole_0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( r2_hidden(sK2(k7_relat_1(sK1,sK0)),k1_xboole_0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(superposition,[],[f180,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(superposition,[],[f58,f45])).

fof(f58,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f40,f21])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f180,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)))
      | k1_xboole_0 = k7_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f125,f21])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1)
      | r2_hidden(sK2(k7_relat_1(X0,X1)),k1_relat_1(k7_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f52,f44])).

fof(f44,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(k7_relat_1(X0,X1)),sK3(k7_relat_1(X0,X1))),k7_relat_1(X0,X1))
      | k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f24,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(f20,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f199,plain,(
    r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f193,f22])).

fof(f22,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f193,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f63,f186])).

fof(f63,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,X1))
      | r1_xboole_0(k1_relat_1(sK1),X1) ) ),
    inference(superposition,[],[f42,f58])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_setfam_1(k1_enumset1(X0,X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (15754)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.49  % (15763)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (15755)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (15763)Refutation not found, incomplete strategy% (15763)------------------------------
% 0.20/0.50  % (15763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (15747)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (15763)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (15763)Memory used [KB]: 10618
% 0.20/0.50  % (15763)Time elapsed: 0.058 s
% 0.20/0.50  % (15763)------------------------------
% 0.20/0.50  % (15763)------------------------------
% 0.20/0.51  % (15769)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (15745)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (15748)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (15747)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f199,f188])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f187])).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.51    inference(backward_demodulation,[],[f20,f186])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f185,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f47,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f10])).
% 0.20/0.51  fof(f10,conjecture,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) )),
% 0.20/0.51    inference(superposition,[],[f39,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),sK0)) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.51    inference(resolution,[],[f41,f19])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f32,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f25,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f27,f37])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    r2_hidden(sK2(k7_relat_1(sK1,sK0)),k1_xboole_0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f184])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    r2_hidden(sK2(k7_relat_1(sK1,sK0)),k1_xboole_0) | k1_xboole_0 = k7_relat_1(sK1,sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.51    inference(superposition,[],[f180,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.51    inference(superposition,[],[f58,f45])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))) )),
% 0.20/0.51    inference(resolution,[],[f40,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    v1_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f30,f37])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK2(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0))) | k1_xboole_0 = k7_relat_1(sK1,X0)) )),
% 0.20/0.51    inference(resolution,[],[f125,f21])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1) | r2_hidden(sK2(k7_relat_1(X0,X1)),k1_relat_1(k7_relat_1(X0,X1)))) )),
% 0.20/0.51    inference(resolution,[],[f52,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.20/0.51    inference(equality_resolution,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(k7_relat_1(X0,X1)),sK3(k7_relat_1(X0,X1))),k7_relat_1(X0,X1)) | k1_xboole_0 = k7_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(resolution,[],[f24,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    k1_xboole_0 != k7_relat_1(sK1,sK0) | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f193,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    k1_xboole_0 != k1_relat_1(k1_xboole_0) | r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.51    inference(superposition,[],[f63,f186])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,X1)) | r1_xboole_0(k1_relat_1(sK1),X1)) )),
% 0.20/0.51    inference(superposition,[],[f42,f58])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != k1_setfam_1(k1_enumset1(X0,X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f31,f37])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (15747)------------------------------
% 0.20/0.51  % (15747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (15747)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (15747)Memory used [KB]: 6396
% 0.20/0.51  % (15747)Time elapsed: 0.066 s
% 0.20/0.51  % (15747)------------------------------
% 0.20/0.51  % (15747)------------------------------
% 0.20/0.51  % (15746)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (15740)Success in time 0.159 s
%------------------------------------------------------------------------------
