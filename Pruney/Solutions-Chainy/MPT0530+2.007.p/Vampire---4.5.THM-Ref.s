%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  93 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :  132 ( 214 expanded)
%              Number of equality atoms :   44 (  73 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f38,f43,f47,f53,f57,f66,f92,f97,f102])).

fof(f102,plain,
    ( spl3_4
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl3_4
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f98,f42])).

% (6958)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% (6963)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f42,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_4
  <=> k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f98,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(superposition,[],[f96,f65])).

fof(f65,plain,
    ( sK0 = k1_setfam_1(k2_tarski(sK0,sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_8
  <=> sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f96,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k1_setfam_1(k2_tarski(X0,X1)),sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_13
  <=> ! [X1,X0] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k1_setfam_1(k2_tarski(X0,X1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f97,plain,
    ( spl3_13
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f93,f90,f26,f95])).

fof(f26,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f90,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k1_setfam_1(k2_tarski(X0,X1)),X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

% (6953)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f93,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k1_setfam_1(k2_tarski(X0,X1)),sK2)
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(resolution,[],[f91,f28])).

fof(f28,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f91,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k1_setfam_1(k2_tarski(X0,X1)),X2) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f24,f90])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k1_setfam_1(k2_tarski(X0,X1)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

fof(f66,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f61,f55,f50,f36,f63])).

fof(f36,plain,
    ( spl3_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f50,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f55,plain,
    ( spl3_7
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f61,plain,
    ( sK0 = k1_setfam_1(k2_tarski(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f60,f37])).

fof(f37,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f60,plain,
    ( k1_setfam_1(k2_tarski(sK0,sK1)) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f56,f52])).

fof(f52,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f56,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f57,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f53,plain,
    ( spl3_6
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f48,f45,f31,f50])).

fof(f31,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f48,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f47,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f43,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f18,f36])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f34,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (6950)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (6955)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (6952)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (6956)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (6955)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f29,f34,f38,f43,f47,f53,f57,f66,f92,f97,f102])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    spl3_4 | ~spl3_8 | ~spl3_13),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f101])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    $false | (spl3_4 | ~spl3_8 | ~spl3_13)),
% 0.20/0.48    inference(subsumption_resolution,[],[f98,f42])).
% 0.20/0.48  % (6958)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (6963)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) | spl3_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    spl3_4 <=> k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2) | (~spl3_8 | ~spl3_13)),
% 0.20/0.48    inference(superposition,[],[f96,f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) | ~spl3_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f63])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl3_8 <=> sK0 = k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k1_setfam_1(k2_tarski(X0,X1)),sK2)) ) | ~spl3_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f95])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    spl3_13 <=> ! [X1,X0] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k1_setfam_1(k2_tarski(X0,X1)),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    spl3_13 | ~spl3_1 | ~spl3_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f93,f90,f26,f95])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    spl3_1 <=> v1_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    spl3_12 <=> ! [X1,X0,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k1_setfam_1(k2_tarski(X0,X1)),X2) | ~v1_relat_1(X2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.48  % (6953)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k1_setfam_1(k2_tarski(X0,X1)),sK2)) ) | (~spl3_1 | ~spl3_12)),
% 0.20/0.48    inference(resolution,[],[f91,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    v1_relat_1(sK2) | ~spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f26])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k1_setfam_1(k2_tarski(X0,X1)),X2)) ) | ~spl3_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f90])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    spl3_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f24,f90])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k1_setfam_1(k2_tarski(X0,X1)),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f22,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    spl3_8 | ~spl3_3 | ~spl3_6 | ~spl3_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f61,f55,f50,f36,f63])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    spl3_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    spl3_7 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) | (~spl3_3 | ~spl3_6 | ~spl3_7)),
% 0.20/0.48    inference(forward_demodulation,[],[f60,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f36])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    k1_setfam_1(k2_tarski(sK0,sK1)) = k4_xboole_0(sK0,k1_xboole_0) | (~spl3_6 | ~spl3_7)),
% 0.20/0.48    inference(superposition,[],[f56,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f50])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) ) | ~spl3_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f55])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    spl3_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f23,f55])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f20,f19])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    spl3_6 | ~spl3_2 | ~spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f48,f45,f31,f50])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    spl3_5 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_2 | ~spl3_5)),
% 0.20/0.48    inference(resolution,[],[f46,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f31])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f45])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f21,f45])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ~spl3_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f17,f40])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)))),
% 0.20/0.48    inference(negated_conjecture,[],[f6])).
% 0.20/0.48  fof(f6,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f18,f36])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f16,f31])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    r1_tarski(sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    spl3_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f15,f26])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (6955)------------------------------
% 0.20/0.48  % (6955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (6955)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (6955)Memory used [KB]: 6140
% 0.20/0.48  % (6955)Time elapsed: 0.060 s
% 0.20/0.48  % (6955)------------------------------
% 0.20/0.48  % (6955)------------------------------
% 0.20/0.48  % (6947)Success in time 0.118 s
%------------------------------------------------------------------------------
