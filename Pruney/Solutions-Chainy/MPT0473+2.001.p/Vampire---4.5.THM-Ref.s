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
% DateTime   : Thu Dec  3 12:48:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 132 expanded)
%              Number of leaves         :   20 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  235 ( 396 expanded)
%              Number of equality atoms :   47 ( 115 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f39,f44,f49,f53,f57,f61,f65,f69,f75,f81,f125,f136,f137,f156])).

fof(f156,plain,
    ( ~ spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_9
    | spl1_18 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_9
    | spl1_18 ),
    inference(subsumption_resolution,[],[f154,f123])).

fof(f123,plain,
    ( ~ v1_xboole_0(sK0)
    | spl1_18 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl1_18
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f154,plain,
    ( v1_xboole_0(sK0)
    | ~ spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f153,f43])).

fof(f43,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl1_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f153,plain,
    ( ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl1_1
    | ~ spl1_4
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f152,f48])).

fof(f48,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl1_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f152,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl1_1
    | ~ spl1_9 ),
    inference(superposition,[],[f68,f32])).

fof(f32,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl1_1
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl1_9
  <=> ! [X0] :
        ( ~ v1_xboole_0(k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f137,plain,
    ( spl1_2
    | ~ spl1_11
    | ~ spl1_18 ),
    inference(avatar_split_clause,[],[f126,f122,f79,f35])).

fof(f35,plain,
    ( spl1_2
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f79,plain,
    ( spl1_11
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k2_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f126,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_11
    | ~ spl1_18 ),
    inference(resolution,[],[f124,f80])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k2_relat_1(X0) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f124,plain,
    ( v1_xboole_0(sK0)
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f122])).

fof(f136,plain,
    ( spl1_1
    | ~ spl1_10
    | ~ spl1_18 ),
    inference(avatar_split_clause,[],[f127,f122,f73,f31])).

fof(f73,plain,
    ( spl1_10
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f127,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl1_10
    | ~ spl1_18 ),
    inference(resolution,[],[f124,f74])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f125,plain,
    ( spl1_18
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f120,f63,f46,f41,f35,f122])).

fof(f63,plain,
    ( spl1_8
  <=> ! [X0] :
        ( ~ v1_xboole_0(k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f120,plain,
    ( v1_xboole_0(sK0)
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f119,f43])).

fof(f119,plain,
    ( ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f117,f48])).

fof(f117,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl1_2
    | ~ spl1_8 ),
    inference(superposition,[],[f64,f36])).

fof(f36,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f81,plain,
    ( spl1_11
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f76,f59,f51,f79])).

fof(f51,plain,
    ( spl1_5
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f59,plain,
    ( spl1_7
  <=> ! [X0] :
        ( v1_xboole_0(k2_relat_1(X0))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f76,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k2_relat_1(X0) )
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(resolution,[],[f60,f52])).

fof(f52,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f60,plain,
    ( ! [X0] :
        ( v1_xboole_0(k2_relat_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f75,plain,
    ( spl1_10
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f71,f55,f51,f73])).

fof(f55,plain,
    ( spl1_6
  <=> ! [X0] :
        ( v1_xboole_0(k1_relat_1(X0))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f71,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(resolution,[],[f56,f52])).

fof(f56,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_relat_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f69,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f65,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f61,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f57,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f53,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f49,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f44,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( k1_xboole_0 != k2_relat_1(sK0)
      | k1_xboole_0 != k1_relat_1(sK0) )
    & ( k1_xboole_0 = k2_relat_1(sK0)
      | k1_xboole_0 = k1_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k2_relat_1(sK0)
        | k1_xboole_0 != k1_relat_1(sK0) )
      & ( k1_xboole_0 = k2_relat_1(sK0)
        | k1_xboole_0 = k1_relat_1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0) )
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0) )
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <~> k1_xboole_0 = k2_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k1_relat_1(X0)
        <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f39,plain,
    ( spl1_1
    | spl1_2 ),
    inference(avatar_split_clause,[],[f22,f35,f31])).

fof(f22,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f23,f35,f31])).

fof(f23,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 != k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (21393)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (21394)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (21397)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.43  % (21397)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f157,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f38,f39,f44,f49,f53,f57,f61,f65,f69,f75,f81,f125,f136,f137,f156])).
% 0.20/0.43  fof(f156,plain,(
% 0.20/0.43    ~spl1_1 | ~spl1_3 | ~spl1_4 | ~spl1_9 | spl1_18),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f155])).
% 0.20/0.43  fof(f155,plain,(
% 0.20/0.43    $false | (~spl1_1 | ~spl1_3 | ~spl1_4 | ~spl1_9 | spl1_18)),
% 0.20/0.43    inference(subsumption_resolution,[],[f154,f123])).
% 0.20/0.43  fof(f123,plain,(
% 0.20/0.43    ~v1_xboole_0(sK0) | spl1_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f122])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    spl1_18 <=> v1_xboole_0(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.20/0.43  fof(f154,plain,(
% 0.20/0.43    v1_xboole_0(sK0) | (~spl1_1 | ~spl1_3 | ~spl1_4 | ~spl1_9)),
% 0.20/0.43    inference(subsumption_resolution,[],[f153,f43])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    v1_relat_1(sK0) | ~spl1_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    spl1_3 <=> v1_relat_1(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.43  fof(f153,plain,(
% 0.20/0.43    ~v1_relat_1(sK0) | v1_xboole_0(sK0) | (~spl1_1 | ~spl1_4 | ~spl1_9)),
% 0.20/0.43    inference(subsumption_resolution,[],[f152,f48])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0) | ~spl1_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f46])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    spl1_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.43  fof(f152,plain,(
% 0.20/0.43    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK0) | v1_xboole_0(sK0) | (~spl1_1 | ~spl1_9)),
% 0.20/0.43    inference(superposition,[],[f68,f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    k1_xboole_0 = k1_relat_1(sK0) | ~spl1_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    spl1_1 <=> k1_xboole_0 = k1_relat_1(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) ) | ~spl1_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f67])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    spl1_9 <=> ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.20/0.43  fof(f137,plain,(
% 0.20/0.43    spl1_2 | ~spl1_11 | ~spl1_18),
% 0.20/0.43    inference(avatar_split_clause,[],[f126,f122,f79,f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    spl1_2 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    spl1_11 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.20/0.43  fof(f126,plain,(
% 0.20/0.43    k1_xboole_0 = k2_relat_1(sK0) | (~spl1_11 | ~spl1_18)),
% 0.20/0.43    inference(resolution,[],[f124,f80])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_relat_1(X0)) ) | ~spl1_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f79])).
% 0.20/0.43  fof(f124,plain,(
% 0.20/0.43    v1_xboole_0(sK0) | ~spl1_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f122])).
% 0.20/0.43  fof(f136,plain,(
% 0.20/0.43    spl1_1 | ~spl1_10 | ~spl1_18),
% 0.20/0.43    inference(avatar_split_clause,[],[f127,f122,f73,f31])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    spl1_10 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.20/0.43  fof(f127,plain,(
% 0.20/0.43    k1_xboole_0 = k1_relat_1(sK0) | (~spl1_10 | ~spl1_18)),
% 0.20/0.43    inference(resolution,[],[f124,f74])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k1_relat_1(X0)) ) | ~spl1_10),
% 0.20/0.44    inference(avatar_component_clause,[],[f73])).
% 0.20/0.44  fof(f125,plain,(
% 0.20/0.44    spl1_18 | ~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_8),
% 0.20/0.44    inference(avatar_split_clause,[],[f120,f63,f46,f41,f35,f122])).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    spl1_8 <=> ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.44  fof(f120,plain,(
% 0.20/0.44    v1_xboole_0(sK0) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_8)),
% 0.20/0.44    inference(subsumption_resolution,[],[f119,f43])).
% 0.20/0.44  fof(f119,plain,(
% 0.20/0.44    ~v1_relat_1(sK0) | v1_xboole_0(sK0) | (~spl1_2 | ~spl1_4 | ~spl1_8)),
% 0.20/0.44    inference(subsumption_resolution,[],[f117,f48])).
% 0.20/0.44  fof(f117,plain,(
% 0.20/0.44    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK0) | v1_xboole_0(sK0) | (~spl1_2 | ~spl1_8)),
% 0.20/0.44    inference(superposition,[],[f64,f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    k1_xboole_0 = k2_relat_1(sK0) | ~spl1_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f35])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) ) | ~spl1_8),
% 0.20/0.44    inference(avatar_component_clause,[],[f63])).
% 0.20/0.44  fof(f81,plain,(
% 0.20/0.44    spl1_11 | ~spl1_5 | ~spl1_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f76,f59,f51,f79])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    spl1_5 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    spl1_7 <=> ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.44  fof(f76,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_relat_1(X0)) ) | (~spl1_5 | ~spl1_7)),
% 0.20/0.44    inference(resolution,[],[f60,f52])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl1_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f51])).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) ) | ~spl1_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f59])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    spl1_10 | ~spl1_5 | ~spl1_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f71,f55,f51,f73])).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    spl1_6 <=> ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.44  fof(f71,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k1_relat_1(X0)) ) | (~spl1_5 | ~spl1_6)),
% 0.20/0.44    inference(resolution,[],[f56,f52])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) ) | ~spl1_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f55])).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    spl1_9),
% 0.20/0.44    inference(avatar_split_clause,[],[f29,f67])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.44    inference(flattening,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    spl1_8),
% 0.20/0.44    inference(avatar_split_clause,[],[f28,f63])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.44    inference(flattening,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.20/0.44  fof(f61,plain,(
% 0.20/0.44    spl1_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f27,f59])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    spl1_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f26,f55])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    spl1_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f25,f51])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    spl1_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f24,f46])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    spl1_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f21,f41])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    v1_relat_1(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    (k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 != k1_relat_1(sK0)) & (k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ? [X0] : ((k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 != k1_relat_1(sK0)) & (k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ? [X0] : ((k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ? [X0] : (((k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0))) & v1_relat_1(X0))),
% 0.20/0.44    inference(nnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ? [X0] : ((k1_xboole_0 = k1_relat_1(X0) <~> k1_xboole_0 = k2_relat_1(X0)) & v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,negated_conjecture,(
% 0.20/0.44    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.44    inference(negated_conjecture,[],[f7])).
% 0.20/0.44  fof(f7,conjecture,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    spl1_1 | spl1_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f22,f35,f31])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ~spl1_1 | ~spl1_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f23,f35,f31])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 != k1_relat_1(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (21397)------------------------------
% 0.20/0.44  % (21397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (21397)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (21397)Memory used [KB]: 6140
% 0.20/0.44  % (21397)Time elapsed: 0.007 s
% 0.20/0.44  % (21397)------------------------------
% 0.20/0.44  % (21397)------------------------------
% 0.20/0.44  % (21386)Success in time 0.081 s
%------------------------------------------------------------------------------
