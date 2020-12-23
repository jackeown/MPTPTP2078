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
% DateTime   : Thu Dec  3 12:56:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 (  92 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  117 ( 184 expanded)
%              Number of equality atoms :   32 (  62 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f73,f76,f87,f93])).

fof(f93,plain,(
    spl1_7 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl1_7 ),
    inference(resolution,[],[f91,f19])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK0 != k2_wellord1(sK0,k3_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( k2_wellord1(X0,k3_relat_1(X0)) != X0
        & v1_relat_1(X0) )
   => ( sK0 != k2_wellord1(sK0,k3_relat_1(sK0))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord1)).

fof(f91,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_7 ),
    inference(resolution,[],[f86,f39])).

fof(f39,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(X1),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f29,f28])).

% (6508)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f28,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f21,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f86,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0))
    | spl1_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl1_7
  <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f87,plain,
    ( ~ spl1_2
    | ~ spl1_7
    | spl1_3 ),
    inference(avatar_split_clause,[],[f82,f50,f84,f46])).

fof(f46,plain,
    ( spl1_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f50,plain,
    ( spl1_3
  <=> sK0 = k7_relat_1(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f82,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(trivial_inequality_removal,[],[f81])).

% (6511)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f81,plain,
    ( sK0 != sK0
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(superposition,[],[f52,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

% (6510)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f52,plain,
    ( sK0 != k7_relat_1(sK0,k3_relat_1(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f76,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl1_1 ),
    inference(resolution,[],[f74,f19])).

fof(f74,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_1 ),
    inference(resolution,[],[f44,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f30,f28])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[],[f29,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f44,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl1_1
  <=> r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f73,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl1_2 ),
    inference(resolution,[],[f48,f19])).

fof(f48,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f53,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f40,f50,f46,f42])).

fof(f40,plain,
    ( sK0 != k7_relat_1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(superposition,[],[f20,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

fof(f20,plain,(
    sK0 != k2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:19:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (6509)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (6509)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (6518)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f53,f73,f76,f87,f93])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    spl1_7),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f92])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    $false | spl1_7),
% 0.22/0.48    inference(resolution,[],[f91,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    v1_relat_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    sK0 != k2_wellord1(sK0,k3_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0] : (k2_wellord1(X0,k3_relat_1(X0)) != X0 & v1_relat_1(X0)) => (sK0 != k2_wellord1(sK0,k3_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0] : (k2_wellord1(X0,k3_relat_1(X0)) != X0 & v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (v1_relat_1(X0) => k2_wellord1(X0,k3_relat_1(X0)) = X0)),
% 0.22/0.48    inference(negated_conjecture,[],[f8])).
% 0.22/0.48  fof(f8,conjecture,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => k2_wellord1(X0,k3_relat_1(X0)) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord1)).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ~v1_relat_1(sK0) | spl1_7),
% 0.22/0.48    inference(resolution,[],[f86,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X1] : (r1_tarski(k1_relat_1(X1),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(superposition,[],[f29,f28])).
% 0.22/0.48  % (6508)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f21,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f22,f24])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0)) | spl1_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f84])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl1_7 <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ~spl1_2 | ~spl1_7 | spl1_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f82,f50,f84,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl1_2 <=> v1_relat_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    spl1_3 <=> sK0 = k7_relat_1(sK0,k3_relat_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0)) | ~v1_relat_1(sK0) | spl1_3),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f81])).
% 0.22/0.48  % (6511)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    sK0 != sK0 | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0)) | ~v1_relat_1(sK0) | spl1_3),
% 0.22/0.48    inference(superposition,[],[f52,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  % (6510)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    sK0 != k7_relat_1(sK0,k3_relat_1(sK0)) | spl1_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f50])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    spl1_1),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    $false | spl1_1),
% 0.22/0.48    inference(resolution,[],[f74,f19])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ~v1_relat_1(sK0) | spl1_1),
% 0.22/0.48    inference(resolution,[],[f44,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(superposition,[],[f30,f28])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 0.22/0.48    inference(superposition,[],[f29,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0)) | spl1_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    spl1_1 <=> r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    spl1_2),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    $false | spl1_2),
% 0.22/0.48    inference(resolution,[],[f48,f19])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ~v1_relat_1(sK0) | spl1_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f46])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ~spl1_1 | ~spl1_2 | ~spl1_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f40,f50,f46,f42])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    sK0 != k7_relat_1(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0) | ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0))),
% 0.22/0.48    inference(superposition,[],[f20,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(superposition,[],[f25,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    sK0 != k2_wellord1(sK0,k3_relat_1(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (6509)------------------------------
% 0.22/0.48  % (6509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (6509)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (6509)Memory used [KB]: 6140
% 0.22/0.48  % (6509)Time elapsed: 0.053 s
% 0.22/0.48  % (6509)------------------------------
% 0.22/0.48  % (6509)------------------------------
% 0.22/0.48  % (6504)Success in time 0.117 s
%------------------------------------------------------------------------------
