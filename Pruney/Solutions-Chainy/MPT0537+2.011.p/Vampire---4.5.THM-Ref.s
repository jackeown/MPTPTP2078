%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 (  89 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :  154 ( 222 expanded)
%              Number of equality atoms :   37 (  55 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f46,f50,f58,f64,f70,f81,f119,f133])).

fof(f133,plain,
    ( spl1_1
    | ~ spl1_4
    | ~ spl1_12
    | ~ spl1_18 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl1_1
    | ~ spl1_4
    | ~ spl1_12
    | ~ spl1_18 ),
    inference(subsumption_resolution,[],[f131,f26])).

fof(f26,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl1_1
  <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f131,plain,
    ( k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)
    | ~ spl1_4
    | ~ spl1_12
    | ~ spl1_18 ),
    inference(forward_demodulation,[],[f128,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl1_12
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f128,plain,
    ( k8_relat_1(k1_xboole_0,sK0) = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_18 ),
    inference(superposition,[],[f118,f41])).

fof(f41,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl1_4
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f118,plain,
    ( ! [X0] : k8_relat_1(X0,sK0) = k5_relat_1(sK0,k6_relat_1(X0))
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl1_18
  <=> ! [X0] : k8_relat_1(X0,sK0) = k5_relat_1(sK0,k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f119,plain,
    ( spl1_18
    | ~ spl1_2
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f113,f48,f29,f117])).

fof(f29,plain,
    ( spl1_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f48,plain,
    ( spl1_6
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f113,plain,
    ( ! [X0] : k8_relat_1(X0,sK0) = k5_relat_1(sK0,k6_relat_1(X0))
    | ~ spl1_2
    | ~ spl1_6 ),
    inference(resolution,[],[f49,f31])).

fof(f31,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f81,plain,
    ( spl1_12
    | ~ spl1_3
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f75,f68,f34,f78])).

fof(f34,plain,
    ( spl1_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f68,plain,
    ( spl1_10
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k5_relat_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f75,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_10 ),
    inference(resolution,[],[f69,f36])).

fof(f36,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k5_relat_1(sK0,X0) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f70,plain,
    ( spl1_10
    | ~ spl1_2
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f65,f62,f29,f68])).

fof(f62,plain,
    ( spl1_9
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = k5_relat_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k5_relat_1(sK0,X0) )
    | ~ spl1_2
    | ~ spl1_9 ),
    inference(resolution,[],[f63,f31])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = k5_relat_1(X0,X1) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,
    ( spl1_9
    | ~ spl1_5
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f60,f56,f44,f62])).

fof(f44,plain,
    ( spl1_5
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f56,plain,
    ( spl1_8
  <=> ! [X1,X0] :
        ( v1_xboole_0(k5_relat_1(X1,X0))
        | ~ v1_relat_1(X1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = k5_relat_1(X0,X1) )
    | ~ spl1_5
    | ~ spl1_8 ),
    inference(resolution,[],[f57,f45])).

fof(f45,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k5_relat_1(X1,X0))
        | ~ v1_relat_1(X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f58,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f21,f56])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X1,X0))
        & v1_xboole_0(k5_relat_1(X1,X0)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X1,X0))
        & v1_xboole_0(k5_relat_1(X1,X0)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_xboole_0(X0) )
     => ( v1_relat_1(k5_relat_1(X1,X0))
        & v1_xboole_0(k5_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_relat_1)).

fof(f50,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f46,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f42,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f37,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f32,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

% (26099)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

fof(f27,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f16,f24])).

fof(f16,plain,(
    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (26103)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (26101)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.43  % (26102)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (26102)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f136,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f46,f50,f58,f64,f70,f81,f119,f133])).
% 0.22/0.43  fof(f133,plain,(
% 0.22/0.43    spl1_1 | ~spl1_4 | ~spl1_12 | ~spl1_18),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f132])).
% 0.22/0.43  fof(f132,plain,(
% 0.22/0.43    $false | (spl1_1 | ~spl1_4 | ~spl1_12 | ~spl1_18)),
% 0.22/0.43    inference(subsumption_resolution,[],[f131,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    spl1_1 <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.43  fof(f131,plain,(
% 0.22/0.43    k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) | (~spl1_4 | ~spl1_12 | ~spl1_18)),
% 0.22/0.43    inference(forward_demodulation,[],[f128,f80])).
% 0.22/0.43  fof(f80,plain,(
% 0.22/0.43    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl1_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f78])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    spl1_12 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.22/0.43  fof(f128,plain,(
% 0.22/0.43    k8_relat_1(k1_xboole_0,sK0) = k5_relat_1(sK0,k1_xboole_0) | (~spl1_4 | ~spl1_18)),
% 0.22/0.43    inference(superposition,[],[f118,f41])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f39])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    spl1_4 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.43  fof(f118,plain,(
% 0.22/0.43    ( ! [X0] : (k8_relat_1(X0,sK0) = k5_relat_1(sK0,k6_relat_1(X0))) ) | ~spl1_18),
% 0.22/0.43    inference(avatar_component_clause,[],[f117])).
% 0.22/0.43  fof(f117,plain,(
% 0.22/0.43    spl1_18 <=> ! [X0] : k8_relat_1(X0,sK0) = k5_relat_1(sK0,k6_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.22/0.43  fof(f119,plain,(
% 0.22/0.43    spl1_18 | ~spl1_2 | ~spl1_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f113,f48,f29,f117])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    spl1_2 <=> v1_relat_1(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    spl1_6 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.43  fof(f113,plain,(
% 0.22/0.43    ( ! [X0] : (k8_relat_1(X0,sK0) = k5_relat_1(sK0,k6_relat_1(X0))) ) | (~spl1_2 | ~spl1_6)),
% 0.22/0.43    inference(resolution,[],[f49,f31])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    v1_relat_1(sK0) | ~spl1_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f29])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) ) | ~spl1_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f48])).
% 0.22/0.43  fof(f81,plain,(
% 0.22/0.43    spl1_12 | ~spl1_3 | ~spl1_10),
% 0.22/0.43    inference(avatar_split_clause,[],[f75,f68,f34,f78])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    spl1_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    spl1_10 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k5_relat_1(sK0,X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl1_3 | ~spl1_10)),
% 0.22/0.43    inference(resolution,[],[f69,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0) | ~spl1_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f34])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k5_relat_1(sK0,X0)) ) | ~spl1_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f68])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    spl1_10 | ~spl1_2 | ~spl1_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f65,f62,f29,f68])).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    spl1_9 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_xboole_0(X1) | k1_xboole_0 = k5_relat_1(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k5_relat_1(sK0,X0)) ) | (~spl1_2 | ~spl1_9)),
% 0.22/0.43    inference(resolution,[],[f63,f31])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_xboole_0(X1) | k1_xboole_0 = k5_relat_1(X0,X1)) ) | ~spl1_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f62])).
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    spl1_9 | ~spl1_5 | ~spl1_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f60,f56,f44,f62])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    spl1_5 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    spl1_8 <=> ! [X1,X0] : (v1_xboole_0(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_xboole_0(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_xboole_0(X1) | k1_xboole_0 = k5_relat_1(X0,X1)) ) | (~spl1_5 | ~spl1_8)),
% 0.22/0.43    inference(resolution,[],[f57,f45])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl1_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f44])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_xboole_0(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_xboole_0(X0)) ) | ~spl1_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f56])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    spl1_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f21,f56])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_xboole_0(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1] : ((v1_relat_1(k5_relat_1(X1,X0)) & v1_xboole_0(k5_relat_1(X1,X0))) | ~v1_relat_1(X1) | ~v1_xboole_0(X0))),
% 0.22/0.43    inference(flattening,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1] : ((v1_relat_1(k5_relat_1(X1,X0)) & v1_xboole_0(k5_relat_1(X1,X0))) | (~v1_relat_1(X1) | ~v1_xboole_0(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : ((v1_relat_1(X1) & v1_xboole_0(X0)) => (v1_relat_1(k5_relat_1(X1,X0)) & v1_xboole_0(k5_relat_1(X1,X0))))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_relat_1)).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    spl1_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f20,f48])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    spl1_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f19,f44])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    spl1_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f18,f39])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    spl1_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f17,f34])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    spl1_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f15,f29])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    v1_relat_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0)) => (k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  % (26099)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,negated_conjecture,(
% 0.22/0.43    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.22/0.43    inference(negated_conjecture,[],[f6])).
% 0.22/0.43  fof(f6,conjecture,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ~spl1_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f16,f24])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (26102)------------------------------
% 0.22/0.43  % (26102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (26102)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (26102)Memory used [KB]: 10618
% 0.22/0.43  % (26102)Time elapsed: 0.006 s
% 0.22/0.43  % (26102)------------------------------
% 0.22/0.43  % (26102)------------------------------
% 0.22/0.43  % (26093)Success in time 0.077 s
%------------------------------------------------------------------------------
