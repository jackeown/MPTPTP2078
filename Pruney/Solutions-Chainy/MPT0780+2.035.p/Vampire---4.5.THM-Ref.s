%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 (  99 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :  152 ( 242 expanded)
%              Number of equality atoms :   48 (  77 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f48,f64,f68,f90,f94,f98,f153,f162,f177])).

fof(f177,plain,
    ( spl3_3
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl3_3
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(trivial_inequality_removal,[],[f175])).

fof(f175,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)
    | spl3_3
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f167,f152])).

fof(f152,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_15
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f167,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
    | spl3_3
    | ~ spl3_17 ),
    inference(superposition,[],[f43,f161])).

fof(f161,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl3_17
  <=> ! [X1,X0] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f43,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_3
  <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f162,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f121,f96,f92,f31,f160])).

fof(f31,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f92,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f96,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f121,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0))
    | ~ spl3_1
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f102,f99])).

fof(f99,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1))
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f33,f93])).

fof(f93,plain,
    ( ! [X2,X0,X1] :
        ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f92])).

fof(f33,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f102,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0)
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f33,f97])).

fof(f97,plain,
    ( ! [X2,X0,X1] :
        ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
        | ~ v1_relat_1(X2) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f96])).

fof(f153,plain,
    ( spl3_15
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f128,f87,f66,f46,f150])).

fof(f46,plain,
    ( spl3_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f66,plain,
    ( spl3_9
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f87,plain,
    ( spl3_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f128,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f125,f47])).

fof(f47,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f125,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(superposition,[],[f67,f89])).

fof(f89,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f87])).

fof(f67,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f98,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f29,f96])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

fof(f94,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f28,f92])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

fof(f90,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f71,f62,f36,f87])).

fof(f36,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f62,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f71,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f38,f63])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f38,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f68,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f24,f66])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f64,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f48,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f46])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f44,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

% (14935)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f36])).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f31])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:22:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (14933)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (14933)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (14943)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (14942)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (14940)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (14932)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (14934)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (14941)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f186,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f34,f39,f44,f48,f64,f68,f90,f94,f98,f153,f162,f177])).
% 0.22/0.48  fof(f177,plain,(
% 0.22/0.48    spl3_3 | ~spl3_15 | ~spl3_17),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f176])).
% 0.22/0.48  fof(f176,plain,(
% 0.22/0.48    $false | (spl3_3 | ~spl3_15 | ~spl3_17)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f175])).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) | (spl3_3 | ~spl3_15 | ~spl3_17)),
% 0.22/0.48    inference(forward_demodulation,[],[f167,f152])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f150])).
% 0.22/0.48  fof(f150,plain,(
% 0.22/0.48    spl3_15 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.48  fof(f167,plain,(
% 0.22/0.48    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) | (spl3_3 | ~spl3_17)),
% 0.22/0.48    inference(superposition,[],[f43,f161])).
% 0.22/0.48  fof(f161,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0))) ) | ~spl3_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f160])).
% 0.22/0.48  fof(f160,plain,(
% 0.22/0.48    spl3_17 <=> ! [X1,X0] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) | spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    spl3_3 <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    spl3_17 | ~spl3_1 | ~spl3_12 | ~spl3_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f121,f96,f92,f31,f160])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    spl3_1 <=> v1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    spl3_12 <=> ! [X1,X0,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    spl3_13 <=> ! [X1,X0,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0))) ) | (~spl3_1 | ~spl3_12 | ~spl3_13)),
% 0.22/0.48    inference(forward_demodulation,[],[f102,f99])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1))) ) | (~spl3_1 | ~spl3_12)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f33,f93])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) ) | ~spl3_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f92])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    v1_relat_1(sK2) | ~spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f31])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0)) ) | (~spl3_1 | ~spl3_13)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f33,f97])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) ) | ~spl3_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f96])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    spl3_15 | ~spl3_4 | ~spl3_9 | ~spl3_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f128,f87,f66,f46,f150])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl3_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl3_9 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    spl3_11 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    sK0 = k3_xboole_0(sK0,sK1) | (~spl3_4 | ~spl3_9 | ~spl3_11)),
% 0.22/0.48    inference(forward_demodulation,[],[f125,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f46])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | (~spl3_9 | ~spl3_11)),
% 0.22/0.48    inference(superposition,[],[f67,f89])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f87])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) ) | ~spl3_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f66])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    spl3_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f29,f96])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    spl3_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f28,f92])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    spl3_11 | ~spl3_2 | ~spl3_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f71,f62,f36,f87])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl3_8 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_2 | ~spl3_8)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f38,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f62])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f36])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl3_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f24,f66])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl3_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f26,f62])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.48    inference(nnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f21,f46])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ~spl3_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f20,f41])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  % (14935)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  fof(f10,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 0.22/0.48    inference(negated_conjecture,[],[f9])).
% 0.22/0.48  fof(f9,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f36])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    r1_tarski(sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f31])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    v1_relat_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (14933)------------------------------
% 0.22/0.48  % (14933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (14933)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (14933)Memory used [KB]: 6140
% 0.22/0.48  % (14933)Time elapsed: 0.055 s
% 0.22/0.48  % (14933)------------------------------
% 0.22/0.48  % (14933)------------------------------
% 0.22/0.48  % (14927)Success in time 0.116 s
%------------------------------------------------------------------------------
