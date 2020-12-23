%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 (  75 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 153 expanded)
%              Number of equality atoms :   37 (  54 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f40,f44,f51,f61,f94,f106,f114])).

fof(f114,plain,
    ( spl2_5
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl2_5
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f50,f109])).

fof(f109,plain,
    ( ! [X1] : k6_subset_1(k1_relat_1(sK1),X1) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1)))
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(superposition,[],[f105,f60])).

fof(f60,plain,
    ( ! [X0,X1] : k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k6_subset_1(X0,X1)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_7
  <=> ! [X1,X0] : k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k6_subset_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f105,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl2_14
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f50,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_5
  <=> k6_subset_1(k1_relat_1(sK1),sK0) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f106,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f102,f92,f29,f104])).

fof(f29,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f92,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f102,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(resolution,[],[f93,f31])).

fof(f31,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f26,f92])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f61,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f46,f42,f38,f34,f59])).

fof(f34,plain,
    ( spl2_2
  <=> ! [X1,X0] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f38,plain,
    ( spl2_3
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f42,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( k1_setfam_1(k2_tarski(X0,X1)) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f46,plain,
    ( ! [X0,X1] : k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k6_subset_1(X0,X1)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f45,f39])).

fof(f39,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f45,plain,
    ( ! [X0,X1] : k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(k6_subset_1(X0,X1),X0))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_setfam_1(k2_tarski(X0,X1)) = X0 )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f51,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f16,f48])).

fof(f16,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

fof(f44,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f27,f42])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f40,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f36,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f24,f34])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f32,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (19817)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.45  % (19806)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (19809)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (19807)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (19809)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f115,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f32,f36,f40,f44,f51,f61,f94,f106,f114])).
% 0.20/0.46  fof(f114,plain,(
% 0.20/0.46    spl2_5 | ~spl2_7 | ~spl2_14),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f113])).
% 0.20/0.46  fof(f113,plain,(
% 0.20/0.46    $false | (spl2_5 | ~spl2_7 | ~spl2_14)),
% 0.20/0.46    inference(subsumption_resolution,[],[f50,f109])).
% 0.20/0.46  fof(f109,plain,(
% 0.20/0.46    ( ! [X1] : (k6_subset_1(k1_relat_1(sK1),X1) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1)))) ) | (~spl2_7 | ~spl2_14)),
% 0.20/0.46    inference(superposition,[],[f105,f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k6_subset_1(X0,X1)))) ) | ~spl2_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f59])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    spl2_7 <=> ! [X1,X0] : k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k6_subset_1(X0,X1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) ) | ~spl2_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f104])).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    spl2_14 <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))) | spl2_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    spl2_5 <=> k6_subset_1(k1_relat_1(sK1),sK0) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    spl2_14 | ~spl2_1 | ~spl2_12),
% 0.20/0.46    inference(avatar_split_clause,[],[f102,f92,f29,f104])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    spl2_1 <=> v1_relat_1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    spl2_12 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.46  fof(f102,plain,(
% 0.20/0.46    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) ) | (~spl2_1 | ~spl2_12)),
% 0.20/0.46    inference(resolution,[],[f93,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    v1_relat_1(sK1) | ~spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f29])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) ) | ~spl2_12),
% 0.20/0.46    inference(avatar_component_clause,[],[f92])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    spl2_12),
% 0.20/0.46    inference(avatar_split_clause,[],[f26,f92])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f22,f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    spl2_7 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f46,f42,f38,f34,f59])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    spl2_2 <=> ! [X1,X0] : r1_tarski(k6_subset_1(X0,X1),X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    spl2_3 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    spl2_4 <=> ! [X1,X0] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k6_subset_1(X0,X1)))) ) | (~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.20/0.46    inference(forward_demodulation,[],[f45,f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f38])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(k6_subset_1(X0,X1),X0))) ) | (~spl2_2 | ~spl2_4)),
% 0.20/0.46    inference(resolution,[],[f43,f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) ) | ~spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f34])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) ) | ~spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f42])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ~spl2_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f16,f48])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))) & v1_relat_1(sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))) & v1_relat_1(sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) & v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 0.20/0.46    inference(negated_conjecture,[],[f8])).
% 0.20/0.46  fof(f8,conjecture,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    spl2_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f27,f42])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f23,f20])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    spl2_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f19,f38])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f24,f34])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f17,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    spl2_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f15,f29])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    v1_relat_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (19809)------------------------------
% 0.20/0.46  % (19809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (19809)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (19809)Memory used [KB]: 6140
% 0.20/0.46  % (19809)Time elapsed: 0.056 s
% 0.20/0.46  % (19809)------------------------------
% 0.20/0.46  % (19809)------------------------------
% 0.20/0.46  % (19801)Success in time 0.109 s
%------------------------------------------------------------------------------
