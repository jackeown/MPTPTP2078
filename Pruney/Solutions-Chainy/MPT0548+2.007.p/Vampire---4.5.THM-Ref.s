%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 105 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :    6
%              Number of atoms          :  156 ( 230 expanded)
%              Number of equality atoms :   49 (  75 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f37,f46,f50,f54,f58,f64,f72,f77,f87,f92,f99,f102])).

fof(f102,plain,
    ( spl1_11
    | ~ spl1_15 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl1_11
    | ~ spl1_15 ),
    inference(trivial_inequality_removal,[],[f100])).

fof(f100,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | spl1_11
    | ~ spl1_15 ),
    inference(superposition,[],[f76,f98])).

fof(f98,plain,
    ( ! [X0] : o_0_0_xboole_0 = k9_relat_1(o_0_0_xboole_0,X0)
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl1_15
  <=> ! [X0] : o_0_0_xboole_0 = k9_relat_1(o_0_0_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f76,plain,
    ( o_0_0_xboole_0 != k9_relat_1(o_0_0_xboole_0,sK0)
    | spl1_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl1_11
  <=> o_0_0_xboole_0 = k9_relat_1(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f99,plain,
    ( spl1_15
    | ~ spl1_2
    | ~ spl1_10
    | ~ spl1_13
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f95,f90,f84,f70,f29,f97])).

fof(f29,plain,
    ( spl1_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f70,plain,
    ( spl1_10
  <=> ! [X0] : o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f84,plain,
    ( spl1_13
  <=> o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f90,plain,
    ( spl1_14
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f95,plain,
    ( ! [X0] : o_0_0_xboole_0 = k9_relat_1(o_0_0_xboole_0,X0)
    | ~ spl1_2
    | ~ spl1_10
    | ~ spl1_13
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f94,f86])).

fof(f86,plain,
    ( o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f94,plain,
    ( ! [X0] : k2_relat_1(o_0_0_xboole_0) = k9_relat_1(o_0_0_xboole_0,X0)
    | ~ spl1_2
    | ~ spl1_10
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f93,f71])).

fof(f71,plain,
    ( ! [X0] : o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f93,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(o_0_0_xboole_0,X0)) = k9_relat_1(o_0_0_xboole_0,X0)
    | ~ spl1_2
    | ~ spl1_14 ),
    inference(resolution,[],[f91,f31])).

fof(f31,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) )
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,
    ( spl1_14
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f88,f56,f48,f90])).

fof(f48,plain,
    ( spl1_6
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f56,plain,
    ( spl1_8
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(resolution,[],[f57,f49])).

fof(f49,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f87,plain,
    ( spl1_13
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f68,f61,f34,f84])).

fof(f34,plain,
    ( spl1_3
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f61,plain,
    ( spl1_9
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f68,plain,
    ( o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(superposition,[],[f36,f63])).

fof(f63,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f36,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f77,plain,
    ( ~ spl1_11
    | spl1_1
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f66,f61,f24,f74])).

fof(f24,plain,
    ( spl1_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f66,plain,
    ( o_0_0_xboole_0 != k9_relat_1(o_0_0_xboole_0,sK0)
    | spl1_1
    | ~ spl1_9 ),
    inference(superposition,[],[f26,f63])).

fof(f26,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f72,plain,
    ( spl1_10
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f65,f61,f44,f70])).

fof(f44,plain,
    ( spl1_5
  <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f65,plain,
    ( ! [X0] : o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X0)
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(superposition,[],[f45,f63])).

fof(f45,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f64,plain,
    ( spl1_9
    | ~ spl1_2
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f59,f52,f29,f61])).

fof(f52,plain,
    ( spl1_7
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f59,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl1_2
    | ~ spl1_7 ),
    inference(resolution,[],[f53,f31])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f58,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f22,f56])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f54,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f21,f52])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f50,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f46,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

fof(f37,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f32,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f16,f29])).

fof(f16,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f27,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f15,f24])).

fof(f15,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:52:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (26742)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (26744)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.42  % (26742)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f103,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f27,f32,f37,f46,f50,f54,f58,f64,f72,f77,f87,f92,f99,f102])).
% 0.22/0.42  fof(f102,plain,(
% 0.22/0.42    spl1_11 | ~spl1_15),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f101])).
% 0.22/0.42  fof(f101,plain,(
% 0.22/0.42    $false | (spl1_11 | ~spl1_15)),
% 0.22/0.42    inference(trivial_inequality_removal,[],[f100])).
% 0.22/0.42  fof(f100,plain,(
% 0.22/0.42    o_0_0_xboole_0 != o_0_0_xboole_0 | (spl1_11 | ~spl1_15)),
% 0.22/0.42    inference(superposition,[],[f76,f98])).
% 0.22/0.42  fof(f98,plain,(
% 0.22/0.42    ( ! [X0] : (o_0_0_xboole_0 = k9_relat_1(o_0_0_xboole_0,X0)) ) | ~spl1_15),
% 0.22/0.42    inference(avatar_component_clause,[],[f97])).
% 0.22/0.42  fof(f97,plain,(
% 0.22/0.42    spl1_15 <=> ! [X0] : o_0_0_xboole_0 = k9_relat_1(o_0_0_xboole_0,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.22/0.42  fof(f76,plain,(
% 0.22/0.42    o_0_0_xboole_0 != k9_relat_1(o_0_0_xboole_0,sK0) | spl1_11),
% 0.22/0.42    inference(avatar_component_clause,[],[f74])).
% 0.22/0.42  fof(f74,plain,(
% 0.22/0.42    spl1_11 <=> o_0_0_xboole_0 = k9_relat_1(o_0_0_xboole_0,sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.42  fof(f99,plain,(
% 0.22/0.42    spl1_15 | ~spl1_2 | ~spl1_10 | ~spl1_13 | ~spl1_14),
% 0.22/0.42    inference(avatar_split_clause,[],[f95,f90,f84,f70,f29,f97])).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    spl1_2 <=> v1_xboole_0(o_0_0_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.42  fof(f70,plain,(
% 0.22/0.42    spl1_10 <=> ! [X0] : o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.42  fof(f84,plain,(
% 0.22/0.42    spl1_13 <=> o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.22/0.42  fof(f90,plain,(
% 0.22/0.42    spl1_14 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) | ~v1_xboole_0(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.22/0.42  fof(f95,plain,(
% 0.22/0.42    ( ! [X0] : (o_0_0_xboole_0 = k9_relat_1(o_0_0_xboole_0,X0)) ) | (~spl1_2 | ~spl1_10 | ~spl1_13 | ~spl1_14)),
% 0.22/0.42    inference(forward_demodulation,[],[f94,f86])).
% 0.22/0.42  fof(f86,plain,(
% 0.22/0.42    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) | ~spl1_13),
% 0.22/0.42    inference(avatar_component_clause,[],[f84])).
% 0.22/0.42  fof(f94,plain,(
% 0.22/0.42    ( ! [X0] : (k2_relat_1(o_0_0_xboole_0) = k9_relat_1(o_0_0_xboole_0,X0)) ) | (~spl1_2 | ~spl1_10 | ~spl1_14)),
% 0.22/0.42    inference(forward_demodulation,[],[f93,f71])).
% 0.22/0.42  fof(f71,plain,(
% 0.22/0.42    ( ! [X0] : (o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X0)) ) | ~spl1_10),
% 0.22/0.42    inference(avatar_component_clause,[],[f70])).
% 0.22/0.42  fof(f93,plain,(
% 0.22/0.42    ( ! [X0] : (k2_relat_1(k7_relat_1(o_0_0_xboole_0,X0)) = k9_relat_1(o_0_0_xboole_0,X0)) ) | (~spl1_2 | ~spl1_14)),
% 0.22/0.42    inference(resolution,[],[f91,f31])).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    v1_xboole_0(o_0_0_xboole_0) | ~spl1_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f29])).
% 0.22/0.42  fof(f91,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_xboole_0(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)) ) | ~spl1_14),
% 0.22/0.42    inference(avatar_component_clause,[],[f90])).
% 0.22/0.42  fof(f92,plain,(
% 0.22/0.42    spl1_14 | ~spl1_6 | ~spl1_8),
% 0.22/0.42    inference(avatar_split_clause,[],[f88,f56,f48,f90])).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    spl1_6 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    spl1_8 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.42  fof(f88,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) | ~v1_xboole_0(X0)) ) | (~spl1_6 | ~spl1_8)),
% 0.22/0.42    inference(resolution,[],[f57,f49])).
% 0.22/0.42  fof(f49,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl1_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f48])).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl1_8),
% 0.22/0.42    inference(avatar_component_clause,[],[f56])).
% 0.22/0.42  fof(f87,plain,(
% 0.22/0.42    spl1_13 | ~spl1_3 | ~spl1_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f68,f61,f34,f84])).
% 0.22/0.42  fof(f34,plain,(
% 0.22/0.42    spl1_3 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.42  fof(f61,plain,(
% 0.22/0.42    spl1_9 <=> o_0_0_xboole_0 = k1_xboole_0),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.42  fof(f68,plain,(
% 0.22/0.42    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) | (~spl1_3 | ~spl1_9)),
% 0.22/0.42    inference(superposition,[],[f36,f63])).
% 0.22/0.42  fof(f63,plain,(
% 0.22/0.42    o_0_0_xboole_0 = k1_xboole_0 | ~spl1_9),
% 0.22/0.42    inference(avatar_component_clause,[],[f61])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f34])).
% 0.22/0.42  fof(f77,plain,(
% 0.22/0.42    ~spl1_11 | spl1_1 | ~spl1_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f66,f61,f24,f74])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    spl1_1 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.42  fof(f66,plain,(
% 0.22/0.42    o_0_0_xboole_0 != k9_relat_1(o_0_0_xboole_0,sK0) | (spl1_1 | ~spl1_9)),
% 0.22/0.42    inference(superposition,[],[f26,f63])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f24])).
% 0.22/0.42  fof(f72,plain,(
% 0.22/0.42    spl1_10 | ~spl1_5 | ~spl1_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f65,f61,f44,f70])).
% 0.22/0.42  fof(f44,plain,(
% 0.22/0.42    spl1_5 <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.42  fof(f65,plain,(
% 0.22/0.42    ( ! [X0] : (o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X0)) ) | (~spl1_5 | ~spl1_9)),
% 0.22/0.42    inference(superposition,[],[f45,f63])).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl1_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f44])).
% 0.22/0.42  fof(f64,plain,(
% 0.22/0.42    spl1_9 | ~spl1_2 | ~spl1_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f59,f52,f29,f61])).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    spl1_7 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    o_0_0_xboole_0 = k1_xboole_0 | (~spl1_2 | ~spl1_7)),
% 0.22/0.42    inference(resolution,[],[f53,f31])).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl1_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f52])).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    spl1_8),
% 0.22/0.42    inference(avatar_split_clause,[],[f22,f56])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.42  fof(f54,plain,(
% 0.22/0.42    spl1_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f21,f52])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    spl1_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f20,f48])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    spl1_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f19,f44])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    spl1_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f18,f34])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,axiom,(
% 0.22/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    spl1_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f16,f29])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    v1_xboole_0(o_0_0_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    v1_xboole_0(o_0_0_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    ~spl1_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f15,f24])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    inference(ennf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,negated_conjecture,(
% 0.22/0.42    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    inference(negated_conjecture,[],[f7])).
% 0.22/0.42  fof(f7,conjecture,(
% 0.22/0.42    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (26742)------------------------------
% 0.22/0.42  % (26742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (26742)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (26742)Memory used [KB]: 10618
% 0.22/0.42  % (26742)Time elapsed: 0.007 s
% 0.22/0.42  % (26742)------------------------------
% 0.22/0.42  % (26742)------------------------------
% 0.22/0.43  % (26736)Success in time 0.064 s
%------------------------------------------------------------------------------
