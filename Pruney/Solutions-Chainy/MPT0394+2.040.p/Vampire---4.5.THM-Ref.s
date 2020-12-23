%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:01 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 145 expanded)
%              Number of leaves         :   14 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 204 expanded)
%              Number of equality atoms :   70 ( 153 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f89,f117])).

fof(f117,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f115,f94])).

fof(f94,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_1 ),
    inference(superposition,[],[f40,f56])).

fof(f56,plain,
    ( k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_1
  <=> k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

% (28046)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (28032)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (28046)Refutation not found, incomplete strategy% (28046)------------------------------
% (28046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28046)Termination reason: Refutation not found, incomplete strategy

% (28046)Memory used [KB]: 1663
% (28046)Time elapsed: 0.144 s
% (28046)------------------------------
% (28046)------------------------------
% (28053)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (28047)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f40,plain,(
    ! [X1] : ~ r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f28,f32,f32])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f115,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_1 ),
    inference(superposition,[],[f26,f100])).

fof(f100,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_1 ),
    inference(superposition,[],[f37,f56])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X0) = k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f24,f32,f32,f23])).

fof(f24,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f89,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f87,f65])).

fof(f65,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f40,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f87,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f26,f71])).

fof(f71,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f37,f60])).

fof(f61,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f51,f58,f54])).

fof(f51,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f47])).

fof(f47,plain,
    ( k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1)
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    inference(superposition,[],[f35,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))
      | k1_xboole_0 = k1_enumset1(X1,X1,X1)
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(superposition,[],[f43,f36])).

fof(f36,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f20,f32])).

fof(f20,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X1,X2)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X2)
      | k1_xboole_0 = k1_enumset1(X2,X2,X2)
      | k1_xboole_0 = k1_enumset1(X0,X0,X1) ) ),
    inference(forward_demodulation,[],[f42,f36])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X2,X2,X2))) = k1_setfam_1(k1_enumset1(X0,X1,X2))
      | k1_xboole_0 = k1_enumset1(X2,X2,X2)
      | k1_xboole_0 = k1_enumset1(X0,X0,X1) ) ),
    inference(superposition,[],[f38,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) ),
    inference(definition_unfolding,[],[f29,f33])).

% (28047)Refutation not found, incomplete strategy% (28047)------------------------------
% (28047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) ),
    inference(definition_unfolding,[],[f30,f31,f32])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f35,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f19,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:17:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.47/0.55  % (28030)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.47/0.55  % (28036)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.47/0.55  % (28035)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.55  % (28036)Refutation not found, incomplete strategy% (28036)------------------------------
% 1.47/0.55  % (28036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (28036)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (28036)Memory used [KB]: 10618
% 1.47/0.55  % (28036)Time elapsed: 0.126 s
% 1.47/0.55  % (28036)------------------------------
% 1.47/0.55  % (28036)------------------------------
% 1.47/0.55  % (28035)Refutation not found, incomplete strategy% (28035)------------------------------
% 1.47/0.55  % (28035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (28035)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (28035)Memory used [KB]: 10618
% 1.47/0.55  % (28035)Time elapsed: 0.125 s
% 1.47/0.55  % (28035)------------------------------
% 1.47/0.55  % (28035)------------------------------
% 1.47/0.55  % (28029)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.47/0.56  % (28029)Refutation not found, incomplete strategy% (28029)------------------------------
% 1.47/0.56  % (28029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (28029)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (28029)Memory used [KB]: 6140
% 1.47/0.56  % (28029)Time elapsed: 0.126 s
% 1.47/0.56  % (28029)------------------------------
% 1.47/0.56  % (28029)------------------------------
% 1.47/0.56  % (28027)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.47/0.56  % (28027)Refutation not found, incomplete strategy% (28027)------------------------------
% 1.47/0.56  % (28027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (28027)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (28027)Memory used [KB]: 10618
% 1.47/0.56  % (28027)Time elapsed: 0.136 s
% 1.47/0.56  % (28027)------------------------------
% 1.47/0.56  % (28027)------------------------------
% 1.47/0.56  % (28048)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.47/0.56  % (28048)Refutation not found, incomplete strategy% (28048)------------------------------
% 1.47/0.56  % (28048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (28048)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (28048)Memory used [KB]: 1663
% 1.47/0.56  % (28048)Time elapsed: 0.093 s
% 1.47/0.56  % (28048)------------------------------
% 1.47/0.56  % (28048)------------------------------
% 1.47/0.56  % (28028)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.47/0.56  % (28040)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.47/0.57  % (28040)Refutation not found, incomplete strategy% (28040)------------------------------
% 1.47/0.57  % (28040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (28040)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (28040)Memory used [KB]: 6140
% 1.47/0.57  % (28040)Time elapsed: 0.002 s
% 1.47/0.57  % (28040)------------------------------
% 1.47/0.57  % (28040)------------------------------
% 1.47/0.57  % (28028)Refutation found. Thanks to Tanya!
% 1.47/0.57  % SZS status Theorem for theBenchmark
% 1.47/0.57  % SZS output start Proof for theBenchmark
% 1.47/0.57  fof(f118,plain,(
% 1.47/0.57    $false),
% 1.47/0.57    inference(avatar_sat_refutation,[],[f61,f89,f117])).
% 1.47/0.57  fof(f117,plain,(
% 1.47/0.57    ~spl2_1),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f116])).
% 1.47/0.57  fof(f116,plain,(
% 1.47/0.57    $false | ~spl2_1),
% 1.47/0.57    inference(subsumption_resolution,[],[f115,f94])).
% 1.47/0.57  fof(f94,plain,(
% 1.47/0.57    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_1),
% 1.47/0.57    inference(superposition,[],[f40,f56])).
% 1.47/0.57  fof(f56,plain,(
% 1.47/0.57    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | ~spl2_1),
% 1.47/0.57    inference(avatar_component_clause,[],[f54])).
% 1.47/0.57  fof(f54,plain,(
% 1.47/0.57    spl2_1 <=> k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.47/0.57  % (28046)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.47/0.57  % (28032)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.47/0.57  % (28046)Refutation not found, incomplete strategy% (28046)------------------------------
% 1.47/0.57  % (28046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (28046)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (28046)Memory used [KB]: 1663
% 1.47/0.57  % (28046)Time elapsed: 0.144 s
% 1.47/0.57  % (28046)------------------------------
% 1.47/0.57  % (28046)------------------------------
% 1.47/0.57  % (28053)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.47/0.58  % (28047)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.47/0.58  fof(f40,plain,(
% 1.47/0.58    ( ! [X1] : (~r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))) )),
% 1.47/0.58    inference(equality_resolution,[],[f39])).
% 1.47/0.58  fof(f39,plain,(
% 1.47/0.58    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))) )),
% 1.47/0.58    inference(definition_unfolding,[],[f28,f32,f32])).
% 1.47/0.58  fof(f32,plain,(
% 1.47/0.58    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.47/0.58    inference(definition_unfolding,[],[f21,f23])).
% 1.47/0.58  fof(f23,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f4])).
% 1.47/0.58  fof(f4,axiom,(
% 1.47/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.47/0.58  fof(f21,plain,(
% 1.47/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f3])).
% 1.47/0.58  fof(f3,axiom,(
% 1.47/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.47/0.58  fof(f28,plain,(
% 1.47/0.58    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f15])).
% 1.47/0.58  fof(f15,plain,(
% 1.47/0.58    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.47/0.58    inference(ennf_transformation,[],[f7])).
% 1.47/0.58  fof(f7,axiom,(
% 1.47/0.58    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 1.47/0.58  fof(f115,plain,(
% 1.47/0.58    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_1),
% 1.47/0.58    inference(trivial_inequality_removal,[],[f114])).
% 1.47/0.58  fof(f114,plain,(
% 1.47/0.58    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_1),
% 1.47/0.58    inference(superposition,[],[f26,f100])).
% 1.47/0.58  fof(f100,plain,(
% 1.47/0.58    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_1),
% 1.47/0.58    inference(superposition,[],[f37,f56])).
% 1.47/0.58  fof(f37,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1))) )),
% 1.47/0.58    inference(definition_unfolding,[],[f24,f32,f32,f23])).
% 1.47/0.58  fof(f24,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f8])).
% 1.47/0.58  fof(f8,axiom,(
% 1.47/0.58    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 1.47/0.58  fof(f26,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f18])).
% 1.47/0.58  fof(f18,plain,(
% 1.47/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.47/0.58    inference(nnf_transformation,[],[f1])).
% 1.47/0.58  fof(f1,axiom,(
% 1.47/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.47/0.58  fof(f89,plain,(
% 1.47/0.58    ~spl2_2),
% 1.47/0.58    inference(avatar_contradiction_clause,[],[f88])).
% 1.47/0.58  fof(f88,plain,(
% 1.47/0.58    $false | ~spl2_2),
% 1.47/0.58    inference(subsumption_resolution,[],[f87,f65])).
% 1.47/0.58  fof(f65,plain,(
% 1.47/0.58    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 1.47/0.58    inference(superposition,[],[f40,f60])).
% 1.47/0.58  fof(f60,plain,(
% 1.47/0.58    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~spl2_2),
% 1.47/0.58    inference(avatar_component_clause,[],[f58])).
% 1.47/0.58  fof(f58,plain,(
% 1.47/0.58    spl2_2 <=> k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.47/0.58  fof(f87,plain,(
% 1.47/0.58    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 1.47/0.58    inference(trivial_inequality_removal,[],[f86])).
% 1.47/0.58  fof(f86,plain,(
% 1.47/0.58    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 1.47/0.58    inference(superposition,[],[f26,f71])).
% 1.47/0.58  fof(f71,plain,(
% 1.47/0.58    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 1.47/0.58    inference(superposition,[],[f37,f60])).
% 1.47/0.58  fof(f61,plain,(
% 1.47/0.58    spl2_1 | spl2_2),
% 1.47/0.58    inference(avatar_split_clause,[],[f51,f58,f54])).
% 1.47/0.58  fof(f51,plain,(
% 1.47/0.58    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 1.47/0.58    inference(trivial_inequality_removal,[],[f47])).
% 1.47/0.58  fof(f47,plain,(
% 1.47/0.58    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 1.47/0.58    inference(superposition,[],[f35,f44])).
% 1.47/0.58  fof(f44,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) | k1_xboole_0 = k1_enumset1(X1,X1,X1) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 1.47/0.58    inference(superposition,[],[f43,f36])).
% 1.47/0.58  fof(f36,plain,(
% 1.47/0.58    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 1.47/0.58    inference(definition_unfolding,[],[f20,f32])).
% 1.47/0.58  fof(f20,plain,(
% 1.47/0.58    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.47/0.58    inference(cnf_transformation,[],[f10])).
% 1.47/0.58  fof(f10,axiom,(
% 1.47/0.58    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.47/0.58  fof(f43,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(X0,X1,X2)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X2) | k1_xboole_0 = k1_enumset1(X2,X2,X2) | k1_xboole_0 = k1_enumset1(X0,X0,X1)) )),
% 1.47/0.58    inference(forward_demodulation,[],[f42,f36])).
% 1.47/0.58  fof(f42,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X2,X2,X2))) = k1_setfam_1(k1_enumset1(X0,X1,X2)) | k1_xboole_0 = k1_enumset1(X2,X2,X2) | k1_xboole_0 = k1_enumset1(X0,X0,X1)) )),
% 1.47/0.58    inference(superposition,[],[f38,f34])).
% 1.47/0.58  fof(f34,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))) )),
% 1.47/0.58    inference(definition_unfolding,[],[f29,f33])).
% 1.47/0.58  % (28047)Refutation not found, incomplete strategy% (28047)------------------------------
% 1.47/0.58  % (28047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.58  fof(f33,plain,(
% 1.47/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)))) )),
% 1.47/0.58    inference(definition_unfolding,[],[f30,f31,f32])).
% 1.47/0.58  fof(f31,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.47/0.58    inference(definition_unfolding,[],[f22,f23])).
% 1.47/0.58  fof(f22,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f6])).
% 1.47/0.58  fof(f6,axiom,(
% 1.47/0.58    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.47/0.58  fof(f30,plain,(
% 1.47/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f2])).
% 1.47/0.58  fof(f2,axiom,(
% 1.47/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 1.47/0.58  fof(f29,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f5])).
% 1.47/0.58  fof(f5,axiom,(
% 1.47/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.47/0.58  fof(f38,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.47/0.58    inference(definition_unfolding,[],[f27,f31])).
% 1.47/0.58  fof(f27,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.47/0.58    inference(cnf_transformation,[],[f14])).
% 1.47/0.58  fof(f14,plain,(
% 1.47/0.58    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.47/0.58    inference(ennf_transformation,[],[f9])).
% 1.47/0.58  fof(f9,axiom,(
% 1.47/0.58    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
% 1.47/0.58  fof(f35,plain,(
% 1.47/0.58    k3_xboole_0(sK0,sK1) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),
% 1.47/0.58    inference(definition_unfolding,[],[f19,f23])).
% 1.47/0.58  fof(f19,plain,(
% 1.47/0.58    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.47/0.58    inference(cnf_transformation,[],[f17])).
% 1.47/0.58  fof(f17,plain,(
% 1.47/0.58    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.47/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f16])).
% 1.47/0.58  fof(f16,plain,(
% 1.47/0.58    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.47/0.58    introduced(choice_axiom,[])).
% 1.47/0.58  fof(f13,plain,(
% 1.47/0.58    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 1.47/0.58    inference(ennf_transformation,[],[f12])).
% 1.47/0.58  fof(f12,negated_conjecture,(
% 1.47/0.58    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.47/0.58    inference(negated_conjecture,[],[f11])).
% 1.47/0.58  fof(f11,conjecture,(
% 1.47/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.47/0.58  % SZS output end Proof for theBenchmark
% 1.47/0.58  % (28028)------------------------------
% 1.47/0.58  % (28028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.58  % (28028)Termination reason: Refutation
% 1.47/0.58  
% 1.47/0.58  % (28028)Memory used [KB]: 10746
% 1.47/0.58  % (28028)Time elapsed: 0.139 s
% 1.47/0.58  % (28028)------------------------------
% 1.47/0.58  % (28028)------------------------------
% 1.47/0.58  % (28025)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.47/0.58  % (28024)Success in time 0.21 s
%------------------------------------------------------------------------------
