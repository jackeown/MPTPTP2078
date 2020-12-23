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
% DateTime   : Thu Dec  3 12:48:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 (  86 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 197 expanded)
%              Number of equality atoms :   23 (  50 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f78,f83,f191,f194])).

fof(f194,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl3_13 ),
    inference(resolution,[],[f190,f21])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

fof(f190,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl3_13
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f191,plain,
    ( ~ spl3_13
    | ~ spl3_1
    | spl3_5 ),
    inference(avatar_split_clause,[],[f180,f73,f56,f188])).

fof(f56,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f73,plain,
    ( spl3_5
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f180,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK0,sK1)
    | spl3_5 ),
    inference(resolution,[],[f136,f75])).

fof(f75,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f37,f33])).

fof(f33,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(k2_tarski(X3,X2)) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f31,f30])).

fof(f30,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f24,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2)))),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f32,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f24])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f83,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f79,f20])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_4 ),
    inference(resolution,[],[f71,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f71,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_4
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f78,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f58,f20])).

fof(f58,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f76,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f52,f73,f69])).

fof(f52,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(trivial_inequality_removal,[],[f51])).

fof(f51,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(sK2,sK0)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f22,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f22,plain,(
    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:05:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.46  % (18480)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (18481)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (18482)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (18481)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f195,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f76,f78,f83,f191,f194])).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    spl3_13),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f192])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    $false | spl3_13),
% 0.20/0.47    inference(resolution,[],[f190,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.47    inference(negated_conjecture,[],[f8])).
% 0.20/0.47  fof(f8,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK1) | spl3_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f188])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    spl3_13 <=> r1_tarski(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    ~spl3_13 | ~spl3_1 | spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f180,f73,f56,f188])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    spl3_1 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    spl3_5 <=> r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | ~r1_tarski(sK0,sK1) | spl3_5),
% 0.20/0.47    inference(resolution,[],[f136,f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    ~r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) | spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f73])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X0) | ~v1_relat_1(X2) | ~r1_tarski(X1,X0)) )),
% 0.20/0.47    inference(superposition,[],[f37,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X2,X3] : (k1_setfam_1(k2_tarski(X3,X2)) = X2 | ~r1_tarski(X2,X3)) )),
% 0.20/0.47    inference(superposition,[],[f31,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f23,f24,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f28,f24])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2)))),X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(resolution,[],[f32,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f29,f24])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    spl3_4),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f82])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    $false | spl3_4),
% 0.20/0.47    inference(resolution,[],[f79,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | spl3_4),
% 0.20/0.47    inference(resolution,[],[f71,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl3_4 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl3_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f77])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    $false | spl3_1),
% 0.20/0.47    inference(resolution,[],[f58,f20])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f56])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ~spl3_4 | ~spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f52,f73,f69])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ~r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,sK0) | ~r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.20/0.47    inference(superposition,[],[f22,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (18481)------------------------------
% 0.20/0.47  % (18481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (18481)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (18481)Memory used [KB]: 6140
% 0.20/0.47  % (18481)Time elapsed: 0.054 s
% 0.20/0.47  % (18481)------------------------------
% 0.20/0.47  % (18481)------------------------------
% 0.20/0.47  % (18483)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (18479)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (18476)Success in time 0.113 s
%------------------------------------------------------------------------------
