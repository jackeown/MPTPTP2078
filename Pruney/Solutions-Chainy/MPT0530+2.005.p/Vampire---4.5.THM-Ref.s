%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:01 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   44 (  68 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 146 expanded)
%              Number of equality atoms :   38 (  62 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f491,plain,(
    $false ),
    inference(subsumption_resolution,[],[f472,f19])).

fof(f19,plain,(
    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

fof(f472,plain,(
    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2) ),
    inference(superposition,[],[f43,f466])).

fof(f466,plain,(
    ! [X0] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) ),
    inference(duplicate_literal_removal,[],[f461])).

fof(f461,plain,(
    ! [X0] :
      ( sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,sK1))
      | sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) ) ),
    inference(resolution,[],[f459,f162])).

fof(f162,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK3(X5,X6,X5),X6)
      | k4_xboole_0(X5,X6) = X5 ) ),
    inference(subsumption_resolution,[],[f160,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f160,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK3(X5,X6,X5),X6)
      | ~ r2_hidden(sK3(X5,X6,X5),X5)
      | k4_xboole_0(X5,X6) = X5 ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK3(X5,X6,X5),X6)
      | ~ r2_hidden(sK3(X5,X6,X5),X5)
      | k4_xboole_0(X5,X6) = X5
      | k4_xboole_0(X5,X6) = X5 ) ),
    inference(resolution,[],[f28,f54])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f459,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK3(sK0,X4,sK0),k4_xboole_0(X5,sK1))
      | sK0 = k4_xboole_0(sK0,X4) ) ),
    inference(resolution,[],[f454,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f454,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,X0,sK0),sK1)
      | sK0 = k4_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f56,f18])).

fof(f18,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | k4_xboole_0(X3,X4) = X3
      | r2_hidden(sK3(X3,X4,X3),X5) ) ),
    inference(resolution,[],[f54,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f43,plain,(
    ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK2) ),
    inference(resolution,[],[f41,f17])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ) ),
    inference(forward_demodulation,[],[f37,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f24,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f22,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:20:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.44/0.56  % (14082)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.44/0.56  % (14082)Refutation not found, incomplete strategy% (14082)------------------------------
% 1.44/0.56  % (14082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (14080)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.44/0.56  % (14081)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.44/0.56  % (14098)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.44/0.57  % (14090)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.44/0.57  % (14082)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.57  
% 1.44/0.57  % (14082)Memory used [KB]: 10618
% 1.44/0.57  % (14082)Time elapsed: 0.116 s
% 1.44/0.57  % (14082)------------------------------
% 1.44/0.57  % (14082)------------------------------
% 1.44/0.57  % (14089)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.44/0.57  % (14088)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.61/0.58  % (14097)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.61/0.58  % (14096)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.61/0.58  % (14096)Refutation not found, incomplete strategy% (14096)------------------------------
% 1.61/0.58  % (14096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (14096)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (14096)Memory used [KB]: 10618
% 1.61/0.58  % (14096)Time elapsed: 0.145 s
% 1.61/0.58  % (14096)------------------------------
% 1.61/0.58  % (14096)------------------------------
% 1.61/0.60  % (14080)Refutation found. Thanks to Tanya!
% 1.61/0.60  % SZS status Theorem for theBenchmark
% 1.61/0.61  % SZS output start Proof for theBenchmark
% 1.61/0.61  fof(f491,plain,(
% 1.61/0.61    $false),
% 1.61/0.61    inference(subsumption_resolution,[],[f472,f19])).
% 1.61/0.61  fof(f19,plain,(
% 1.61/0.61    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)),
% 1.61/0.61    inference(cnf_transformation,[],[f14])).
% 1.61/0.61  fof(f14,plain,(
% 1.61/0.61    ? [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.61/0.61    inference(flattening,[],[f13])).
% 1.61/0.61  fof(f13,plain,(
% 1.61/0.61    ? [X0,X1,X2] : ((k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.61/0.61    inference(ennf_transformation,[],[f11])).
% 1.61/0.61  fof(f11,negated_conjecture,(
% 1.61/0.61    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)))),
% 1.61/0.61    inference(negated_conjecture,[],[f10])).
% 1.61/0.61  fof(f10,conjecture,(
% 1.61/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).
% 1.61/0.61  fof(f472,plain,(
% 1.61/0.61    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2)),
% 1.61/0.61    inference(superposition,[],[f43,f466])).
% 1.61/0.61  fof(f466,plain,(
% 1.61/0.61    ( ! [X0] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,sK1))) )),
% 1.61/0.61    inference(duplicate_literal_removal,[],[f461])).
% 1.61/0.61  fof(f461,plain,(
% 1.61/0.61    ( ! [X0] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) | sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,sK1))) )),
% 1.61/0.61    inference(resolution,[],[f459,f162])).
% 1.61/0.61  fof(f162,plain,(
% 1.61/0.61    ( ! [X6,X5] : (r2_hidden(sK3(X5,X6,X5),X6) | k4_xboole_0(X5,X6) = X5) )),
% 1.61/0.61    inference(subsumption_resolution,[],[f160,f54])).
% 1.61/0.61  fof(f54,plain,(
% 1.61/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 1.61/0.61    inference(factoring,[],[f29])).
% 1.61/0.61  fof(f29,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.61/0.61    inference(cnf_transformation,[],[f2])).
% 1.61/0.61  fof(f2,axiom,(
% 1.61/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.61/0.61  fof(f160,plain,(
% 1.61/0.61    ( ! [X6,X5] : (r2_hidden(sK3(X5,X6,X5),X6) | ~r2_hidden(sK3(X5,X6,X5),X5) | k4_xboole_0(X5,X6) = X5) )),
% 1.61/0.61    inference(duplicate_literal_removal,[],[f158])).
% 1.61/0.61  fof(f158,plain,(
% 1.61/0.61    ( ! [X6,X5] : (r2_hidden(sK3(X5,X6,X5),X6) | ~r2_hidden(sK3(X5,X6,X5),X5) | k4_xboole_0(X5,X6) = X5 | k4_xboole_0(X5,X6) = X5) )),
% 1.61/0.61    inference(resolution,[],[f28,f54])).
% 1.61/0.61  fof(f28,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 1.61/0.61    inference(cnf_transformation,[],[f2])).
% 1.61/0.61  fof(f459,plain,(
% 1.61/0.61    ( ! [X4,X5] : (~r2_hidden(sK3(sK0,X4,sK0),k4_xboole_0(X5,sK1)) | sK0 = k4_xboole_0(sK0,X4)) )),
% 1.61/0.61    inference(resolution,[],[f454,f39])).
% 1.61/0.61  fof(f39,plain,(
% 1.61/0.61    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 1.61/0.61    inference(equality_resolution,[],[f32])).
% 1.61/0.61  fof(f32,plain,(
% 1.61/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.61/0.61    inference(cnf_transformation,[],[f2])).
% 1.61/0.61  fof(f454,plain,(
% 1.61/0.61    ( ! [X0] : (r2_hidden(sK3(sK0,X0,sK0),sK1) | sK0 = k4_xboole_0(sK0,X0)) )),
% 1.61/0.61    inference(resolution,[],[f56,f18])).
% 1.61/0.61  fof(f18,plain,(
% 1.61/0.61    r1_tarski(sK0,sK1)),
% 1.61/0.61    inference(cnf_transformation,[],[f14])).
% 1.61/0.61  fof(f56,plain,(
% 1.61/0.61    ( ! [X4,X5,X3] : (~r1_tarski(X3,X5) | k4_xboole_0(X3,X4) = X3 | r2_hidden(sK3(X3,X4,X3),X5)) )),
% 1.61/0.61    inference(resolution,[],[f54,f25])).
% 1.61/0.61  fof(f25,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r1_tarski(X0,X1) | r2_hidden(X2,X1)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f15])).
% 1.61/0.61  fof(f15,plain,(
% 1.61/0.61    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.61/0.61    inference(ennf_transformation,[],[f12])).
% 1.61/0.61  fof(f12,plain,(
% 1.61/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.61/0.61    inference(unused_predicate_definition_removal,[],[f1])).
% 1.61/0.61  fof(f1,axiom,(
% 1.61/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.61/0.61  fof(f43,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK2)) )),
% 1.61/0.61    inference(resolution,[],[f41,f17])).
% 1.61/0.61  fof(f17,plain,(
% 1.61/0.61    v1_relat_1(sK2)),
% 1.61/0.61    inference(cnf_transformation,[],[f14])).
% 1.61/0.61  fof(f41,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.61/0.61    inference(forward_demodulation,[],[f37,f36])).
% 1.61/0.61  fof(f36,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.61/0.61    inference(definition_unfolding,[],[f24,f35])).
% 1.61/0.61  fof(f35,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.61/0.61    inference(definition_unfolding,[],[f22,f34])).
% 1.61/0.61  fof(f34,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.61/0.61    inference(definition_unfolding,[],[f23,f26])).
% 1.61/0.61  fof(f26,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f7])).
% 1.61/0.61  fof(f7,axiom,(
% 1.61/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.61/0.61  fof(f23,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f6])).
% 1.61/0.61  fof(f6,axiom,(
% 1.61/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.61/0.61  fof(f22,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.61/0.61    inference(cnf_transformation,[],[f8])).
% 1.61/0.61  fof(f8,axiom,(
% 1.61/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.61/0.61  fof(f24,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f5])).
% 1.61/0.61  fof(f5,axiom,(
% 1.61/0.61    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.61/0.61  fof(f37,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X2)) )),
% 1.61/0.61    inference(definition_unfolding,[],[f27,f35])).
% 1.61/0.61  fof(f27,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f16])).
% 1.61/0.61  fof(f16,plain,(
% 1.61/0.61    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.61/0.61    inference(ennf_transformation,[],[f9])).
% 1.61/0.61  fof(f9,axiom,(
% 1.61/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).
% 1.61/0.61  % SZS output end Proof for theBenchmark
% 1.61/0.61  % (14080)------------------------------
% 1.61/0.61  % (14080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.61  % (14080)Termination reason: Refutation
% 1.61/0.61  
% 1.61/0.61  % (14080)Memory used [KB]: 6524
% 1.61/0.61  % (14080)Time elapsed: 0.159 s
% 1.61/0.61  % (14080)------------------------------
% 1.61/0.61  % (14080)------------------------------
% 1.61/0.61  % (14073)Success in time 0.239 s
%------------------------------------------------------------------------------
