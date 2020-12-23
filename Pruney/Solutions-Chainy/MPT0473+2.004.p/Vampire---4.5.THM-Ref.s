%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 141 expanded)
%              Number of leaves         :   21 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  241 ( 398 expanded)
%              Number of equality atoms :   57 ( 130 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f38,f43,f48,f53,f57,f61,f65,f70,f76,f82,f92,f98,f104,f107,f118])).

fof(f118,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_11
    | spl2_12 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_11
    | spl2_12 ),
    inference(subsumption_resolution,[],[f116,f90])).

fof(f90,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl2_12
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f116,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f115,f42])).

fof(f42,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f115,plain,
    ( ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f114,f81])).

fof(f81,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f114,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(superposition,[],[f60,f31])).

fof(f31,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_1
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_7
  <=> ! [X0] :
        ( ~ v1_xboole_0(k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f107,plain,
    ( spl2_2
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl2_2
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f105,f47])).

fof(f47,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f105,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl2_2
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f36,f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f36,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_2
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f104,plain,
    ( spl2_1
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl2_1
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f101,f52])).

fof(f52,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f101,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl2_1
    | ~ spl2_13 ),
    inference(superposition,[],[f32,f97])).

fof(f32,plain,
    ( k1_xboole_0 != k1_relat_1(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f98,plain,
    ( spl2_13
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f93,f89,f55,f95])).

fof(f55,plain,
    ( spl2_6
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f93,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(resolution,[],[f91,f56])).

fof(f56,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f91,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f92,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f87,f79,f63,f40,f34,f89])).

fof(f63,plain,
    ( spl2_8
  <=> ! [X0] :
        ( ~ v1_xboole_0(k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f87,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f86,f81])).

fof(f86,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f85,f35])).

fof(f35,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f85,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK0))
    | v1_xboole_0(sK0)
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f64,f42])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(k2_relat_1(X0))
        | v1_xboole_0(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f82,plain,
    ( spl2_11
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f77,f73,f67,f79])).

fof(f67,plain,
    ( spl2_9
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f73,plain,
    ( spl2_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f77,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(superposition,[],[f69,f75])).

fof(f75,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f69,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f76,plain,
    ( spl2_10
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f71,f67,f55,f73])).

fof(f71,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(resolution,[],[f56,f69])).

fof(f70,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f18])).

fof(f18,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK1) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f65,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f61,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f57,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f25,f55])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f53,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f48,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f43,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f20,f40])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( k1_xboole_0 != k2_relat_1(sK0)
      | k1_xboole_0 != k1_relat_1(sK0) )
    & ( k1_xboole_0 = k2_relat_1(sK0)
      | k1_xboole_0 = k1_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f16,plain,
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

fof(f15,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0) )
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0) )
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <~> k1_xboole_0 = k2_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k1_relat_1(X0)
        <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f38,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f21,f34,f30])).

fof(f21,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f22,f34,f30])).

fof(f22,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 != k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:58:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (8054)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (8053)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (8049)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.43  % (8053)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f119,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f37,f38,f43,f48,f53,f57,f61,f65,f70,f76,f82,f92,f98,f104,f107,f118])).
% 0.22/0.43  fof(f118,plain,(
% 0.22/0.43    ~spl2_1 | ~spl2_3 | ~spl2_7 | ~spl2_11 | spl2_12),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f117])).
% 0.22/0.43  fof(f117,plain,(
% 0.22/0.43    $false | (~spl2_1 | ~spl2_3 | ~spl2_7 | ~spl2_11 | spl2_12)),
% 0.22/0.43    inference(subsumption_resolution,[],[f116,f90])).
% 0.22/0.43  fof(f90,plain,(
% 0.22/0.43    ~v1_xboole_0(sK0) | spl2_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f89])).
% 0.22/0.43  fof(f89,plain,(
% 0.22/0.43    spl2_12 <=> v1_xboole_0(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.43  fof(f116,plain,(
% 0.22/0.43    v1_xboole_0(sK0) | (~spl2_1 | ~spl2_3 | ~spl2_7 | ~spl2_11)),
% 0.22/0.43    inference(subsumption_resolution,[],[f115,f42])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    v1_relat_1(sK0) | ~spl2_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f40])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    spl2_3 <=> v1_relat_1(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.43  fof(f115,plain,(
% 0.22/0.43    ~v1_relat_1(sK0) | v1_xboole_0(sK0) | (~spl2_1 | ~spl2_7 | ~spl2_11)),
% 0.22/0.43    inference(subsumption_resolution,[],[f114,f81])).
% 0.22/0.43  fof(f81,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0) | ~spl2_11),
% 0.22/0.43    inference(avatar_component_clause,[],[f79])).
% 0.22/0.43  fof(f79,plain,(
% 0.22/0.43    spl2_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.43  fof(f114,plain,(
% 0.22/0.43    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK0) | v1_xboole_0(sK0) | (~spl2_1 | ~spl2_7)),
% 0.22/0.43    inference(superposition,[],[f60,f31])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    k1_xboole_0 = k1_relat_1(sK0) | ~spl2_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    spl2_1 <=> k1_xboole_0 = k1_relat_1(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) ) | ~spl2_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f59])).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    spl2_7 <=> ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.43  fof(f107,plain,(
% 0.22/0.43    spl2_2 | ~spl2_4 | ~spl2_13),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f106])).
% 0.22/0.43  fof(f106,plain,(
% 0.22/0.43    $false | (spl2_2 | ~spl2_4 | ~spl2_13)),
% 0.22/0.43    inference(subsumption_resolution,[],[f105,f47])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl2_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f45])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    spl2_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.43  fof(f105,plain,(
% 0.22/0.43    k1_xboole_0 != k2_relat_1(k1_xboole_0) | (spl2_2 | ~spl2_13)),
% 0.22/0.43    inference(forward_demodulation,[],[f36,f97])).
% 0.22/0.43  fof(f97,plain,(
% 0.22/0.43    k1_xboole_0 = sK0 | ~spl2_13),
% 0.22/0.43    inference(avatar_component_clause,[],[f95])).
% 0.22/0.43  fof(f95,plain,(
% 0.22/0.43    spl2_13 <=> k1_xboole_0 = sK0),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    k1_xboole_0 != k2_relat_1(sK0) | spl2_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    spl2_2 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.43  fof(f104,plain,(
% 0.22/0.43    spl2_1 | ~spl2_5 | ~spl2_13),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f103])).
% 0.22/0.43  fof(f103,plain,(
% 0.22/0.43    $false | (spl2_1 | ~spl2_5 | ~spl2_13)),
% 0.22/0.43    inference(subsumption_resolution,[],[f101,f52])).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl2_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f50])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    spl2_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.43  fof(f101,plain,(
% 0.22/0.43    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (spl2_1 | ~spl2_13)),
% 0.22/0.43    inference(superposition,[],[f32,f97])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    k1_xboole_0 != k1_relat_1(sK0) | spl2_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f30])).
% 0.22/0.43  fof(f98,plain,(
% 0.22/0.43    spl2_13 | ~spl2_6 | ~spl2_12),
% 0.22/0.43    inference(avatar_split_clause,[],[f93,f89,f55,f95])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    spl2_6 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.43  fof(f93,plain,(
% 0.22/0.43    k1_xboole_0 = sK0 | (~spl2_6 | ~spl2_12)),
% 0.22/0.43    inference(resolution,[],[f91,f56])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl2_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f55])).
% 0.22/0.43  fof(f91,plain,(
% 0.22/0.43    v1_xboole_0(sK0) | ~spl2_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f89])).
% 0.22/0.43  fof(f92,plain,(
% 0.22/0.43    spl2_12 | ~spl2_2 | ~spl2_3 | ~spl2_8 | ~spl2_11),
% 0.22/0.43    inference(avatar_split_clause,[],[f87,f79,f63,f40,f34,f89])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    spl2_8 <=> ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.43  fof(f87,plain,(
% 0.22/0.43    v1_xboole_0(sK0) | (~spl2_2 | ~spl2_3 | ~spl2_8 | ~spl2_11)),
% 0.22/0.43    inference(subsumption_resolution,[],[f86,f81])).
% 0.22/0.43  fof(f86,plain,(
% 0.22/0.43    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK0) | (~spl2_2 | ~spl2_3 | ~spl2_8)),
% 0.22/0.43    inference(forward_demodulation,[],[f85,f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    k1_xboole_0 = k2_relat_1(sK0) | ~spl2_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f34])).
% 0.22/0.43  fof(f85,plain,(
% 0.22/0.43    ~v1_xboole_0(k2_relat_1(sK0)) | v1_xboole_0(sK0) | (~spl2_3 | ~spl2_8)),
% 0.22/0.43    inference(resolution,[],[f64,f42])).
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_relat_1(X0) | ~v1_xboole_0(k2_relat_1(X0)) | v1_xboole_0(X0)) ) | ~spl2_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f63])).
% 0.22/0.43  fof(f82,plain,(
% 0.22/0.43    spl2_11 | ~spl2_9 | ~spl2_10),
% 0.22/0.43    inference(avatar_split_clause,[],[f77,f73,f67,f79])).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    spl2_9 <=> v1_xboole_0(sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    spl2_10 <=> k1_xboole_0 = sK1),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0) | (~spl2_9 | ~spl2_10)),
% 0.22/0.43    inference(superposition,[],[f69,f75])).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    k1_xboole_0 = sK1 | ~spl2_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f73])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    v1_xboole_0(sK1) | ~spl2_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f67])).
% 0.22/0.43  fof(f76,plain,(
% 0.22/0.43    spl2_10 | ~spl2_6 | ~spl2_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f71,f67,f55,f73])).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    k1_xboole_0 = sK1 | (~spl2_6 | ~spl2_9)),
% 0.22/0.43    inference(resolution,[],[f56,f69])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    spl2_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f28,f67])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    v1_xboole_0(sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    v1_xboole_0(sK1)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK1)),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ? [X0] : v1_xboole_0(X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    spl2_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f27,f63])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.43    inference(flattening,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    spl2_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f26,f59])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.43    inference(flattening,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    spl2_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f25,f55])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    spl2_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f23,f50])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    spl2_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f24,f45])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    spl2_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f20,f40])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    v1_relat_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    (k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 != k1_relat_1(sK0)) & (k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ? [X0] : ((k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 != k1_relat_1(sK0)) & (k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ? [X0] : ((k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ? [X0] : (((k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0))) & v1_relat_1(X0))),
% 0.22/0.43    inference(nnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0] : ((k1_xboole_0 = k1_relat_1(X0) <~> k1_xboole_0 = k2_relat_1(X0)) & v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,negated_conjecture,(
% 0.22/0.43    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.22/0.43    inference(negated_conjecture,[],[f6])).
% 0.22/0.43  fof(f6,conjecture,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    spl2_1 | spl2_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f21,f34,f30])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ~spl2_1 | ~spl2_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f22,f34,f30])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 != k1_relat_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (8053)------------------------------
% 0.22/0.43  % (8053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (8053)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (8053)Memory used [KB]: 10618
% 0.22/0.43  % (8053)Time elapsed: 0.006 s
% 0.22/0.43  % (8053)------------------------------
% 0.22/0.43  % (8053)------------------------------
% 0.22/0.43  % (8047)Success in time 0.073 s
%------------------------------------------------------------------------------
