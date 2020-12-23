%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 117 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :  193 ( 303 expanded)
%              Number of equality atoms :   47 (  77 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32111)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f181,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f49,f55,f59,f68,f74,f78,f84,f90,f95,f172,f178])).

fof(f178,plain,
    ( spl3_5
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl3_5
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f176,f54])).

fof(f54,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_5
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f176,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f173,f94])).

fof(f94,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_13
  <=> k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f173,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK0),sK1) = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl3_9
    | ~ spl3_23 ),
    inference(superposition,[],[f171,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK0,sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_9
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f171,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl3_23
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f172,plain,
    ( spl3_23
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f166,f88,f32,f170])).

fof(f32,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f88,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f166,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(resolution,[],[f89,f34])).

fof(f34,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f89,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f95,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f85,f82,f37,f92])).

fof(f37,plain,
    ( spl3_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f82,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k7_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f85,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(resolution,[],[f83,f39])).

fof(f39,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k7_relat_1(sK2,X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f82])).

fof(f90,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f30,f88])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f84,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f79,f76,f32,f82])).

fof(f76,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_relat_1(X1)
        | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k7_relat_1(sK2,X0) )
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(resolution,[],[f77,f34])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_xboole_0(X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f76])).

fof(f78,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f64,f57,f47,f76])).

fof(f47,plain,
    ( spl3_4
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( v1_xboole_0(k7_relat_1(X0,X1))
        | ~ v1_xboole_0(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_relat_1(X1)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(resolution,[],[f58,f48])).

% (32112)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% (32121)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% (32119)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% (32123)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% (32116)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f48,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k7_relat_1(X0,X1))
        | ~ v1_xboole_0(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f74,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f69,f66,f42,f71])).

fof(f42,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f66,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f69,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f67,f44])).

fof(f44,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f68,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f59,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f57])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

fof(f55,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f21,f52])).

fof(f21,plain,(
    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    & r1_xboole_0(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
        & r1_xboole_0(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
      & r1_xboole_0(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f49,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f37])).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f35,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f19,f32])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:48:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (32117)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.46  % (32113)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.46  % (32114)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (32110)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (32117)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  % (32111)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  fof(f181,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f35,f40,f45,f49,f55,f59,f68,f74,f78,f84,f90,f95,f172,f178])).
% 0.22/0.47  fof(f178,plain,(
% 0.22/0.47    spl3_5 | ~spl3_9 | ~spl3_13 | ~spl3_23),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f177])).
% 0.22/0.47  fof(f177,plain,(
% 0.22/0.47    $false | (spl3_5 | ~spl3_9 | ~spl3_13 | ~spl3_23)),
% 0.22/0.47    inference(subsumption_resolution,[],[f176,f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) | spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f52])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    spl3_5 <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f176,plain,(
% 0.22/0.47    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1) | (~spl3_9 | ~spl3_13 | ~spl3_23)),
% 0.22/0.47    inference(forward_demodulation,[],[f173,f94])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) | ~spl3_13),
% 0.22/0.47    inference(avatar_component_clause,[],[f92])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    spl3_13 <=> k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.47  fof(f173,plain,(
% 0.22/0.47    k7_relat_1(k7_relat_1(sK2,sK0),sK1) = k7_relat_1(sK2,k1_xboole_0) | (~spl3_9 | ~spl3_23)),
% 0.22/0.47    inference(superposition,[],[f171,f73])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    k1_xboole_0 = k1_setfam_1(k2_tarski(sK0,sK1)) | ~spl3_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f71])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    spl3_9 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.47  fof(f171,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))) ) | ~spl3_23),
% 0.22/0.47    inference(avatar_component_clause,[],[f170])).
% 0.22/0.47  fof(f170,plain,(
% 0.22/0.47    spl3_23 <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.47  fof(f172,plain,(
% 0.22/0.47    spl3_23 | ~spl3_1 | ~spl3_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f166,f88,f32,f170])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    spl3_1 <=> v1_relat_1(sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    spl3_12 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.47  fof(f166,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))) ) | (~spl3_1 | ~spl3_12)),
% 0.22/0.47    inference(resolution,[],[f89,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    v1_relat_1(sK2) | ~spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f32])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))) ) | ~spl3_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f88])).
% 0.22/0.47  fof(f95,plain,(
% 0.22/0.47    spl3_13 | ~spl3_2 | ~spl3_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f85,f82,f37,f92])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    spl3_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    spl3_11 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k7_relat_1(sK2,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) | (~spl3_2 | ~spl3_11)),
% 0.22/0.47    inference(resolution,[],[f83,f39])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0) | ~spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f37])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k7_relat_1(sK2,X0)) ) | ~spl3_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f82])).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    spl3_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f30,f88])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f28,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    spl3_11 | ~spl3_1 | ~spl3_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f79,f76,f32,f82])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    spl3_10 <=> ! [X1,X0] : (~v1_xboole_0(X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k7_relat_1(sK2,X0)) ) | (~spl3_1 | ~spl3_10)),
% 0.22/0.47    inference(resolution,[],[f77,f34])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_xboole_0(X0) | k1_xboole_0 = k7_relat_1(X1,X0)) ) | ~spl3_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f76])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    spl3_10 | ~spl3_4 | ~spl3_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f64,f57,f47,f76])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    spl3_4 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    spl3_6 <=> ! [X1,X0] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0)) ) | (~spl3_4 | ~spl3_6)),
% 0.22/0.47    inference(resolution,[],[f58,f48])).
% 0.22/0.47  % (32112)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (32121)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (32119)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (32123)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (32116)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f47])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) ) | ~spl3_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f57])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl3_9 | ~spl3_3 | ~spl3_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f69,f66,f42,f71])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    spl3_3 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl3_8 <=> ! [X1,X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    k1_xboole_0 = k1_setfam_1(k2_tarski(sK0,sK1)) | (~spl3_3 | ~spl3_8)),
% 0.22/0.48    inference(resolution,[],[f67,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    r1_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f42])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) ) | ~spl3_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f66])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl3_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f29,f66])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f27,f24])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    spl3_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f25,f57])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ~spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f21,f52])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.22/0.48    inference(negated_conjecture,[],[f7])).
% 0.22/0.48  fof(f7,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f23,f47])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    spl3_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f20,f42])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    r1_xboole_0(sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f22,f37])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f32])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    v1_relat_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (32117)------------------------------
% 0.22/0.48  % (32117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (32117)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (32117)Memory used [KB]: 6140
% 0.22/0.48  % (32117)Time elapsed: 0.057 s
% 0.22/0.48  % (32117)------------------------------
% 0.22/0.48  % (32117)------------------------------
% 0.22/0.48  % (32125)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (32109)Success in time 0.124 s
%------------------------------------------------------------------------------
