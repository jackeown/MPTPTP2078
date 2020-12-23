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
% DateTime   : Thu Dec  3 12:48:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  79 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :  131 ( 199 expanded)
%              Number of equality atoms :   24 (  41 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f33,f41,f46,f52,f58,f64,f70,f78])).

fof(f78,plain,
    ( spl2_1
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl2_1
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f75,f23])).

fof(f23,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl2_1
  <=> k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f75,plain,
    ( k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0)
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(resolution,[],[f69,f57])).

fof(f57,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_10
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f70,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f65,f62,f26,f68])).

fof(f26,plain,
    ( spl2_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f62,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_relat_1(X1)
        | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) )
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(resolution,[],[f63,f28])).

fof(f28,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_xboole_0(X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f60,f39,f31,f62])).

fof(f31,plain,
    ( spl2_3
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f39,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( v1_xboole_0(k7_relat_1(X0,X1))
        | ~ v1_xboole_0(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_relat_1(X1)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k7_relat_1(X0,X1))
        | ~ v1_xboole_0(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f58,plain,
    ( spl2_8
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f53,f49,f43,f55])).

fof(f43,plain,
    ( spl2_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f49,plain,
    ( spl2_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f53,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f45,f51])).

fof(f51,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f45,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f52,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f47,f43,f31,f49])).

fof(f47,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(resolution,[],[f32,f45])).

fof(f46,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f12])).

fof(f12,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK1) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f41,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

fof(f33,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f29,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k7_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( k1_xboole_0 != k7_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f24,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f15,f21])).

fof(f15,plain,(
    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:46:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (11377)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.42  % (11373)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (11377)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f24,f29,f33,f41,f46,f52,f58,f64,f70,f78])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    spl2_1 | ~spl2_8 | ~spl2_10),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f77])).
% 0.20/0.42  fof(f77,plain,(
% 0.20/0.42    $false | (spl2_1 | ~spl2_8 | ~spl2_10)),
% 0.20/0.42    inference(subsumption_resolution,[],[f75,f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) | spl2_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    spl2_1 <=> k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f75,plain,(
% 0.20/0.42    k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0) | (~spl2_8 | ~spl2_10)),
% 0.20/0.42    inference(resolution,[],[f69,f57])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    v1_xboole_0(k1_xboole_0) | ~spl2_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f55])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    spl2_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k7_relat_1(sK0,X0)) ) | ~spl2_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f68])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    spl2_10 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k7_relat_1(sK0,X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    spl2_10 | ~spl2_2 | ~spl2_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f65,f62,f26,f68])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    spl2_2 <=> v1_relat_1(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    spl2_9 <=> ! [X1,X0] : (~v1_xboole_0(X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k7_relat_1(sK0,X0)) ) | (~spl2_2 | ~spl2_9)),
% 0.20/0.42    inference(resolution,[],[f63,f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    v1_relat_1(sK0) | ~spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f26])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_xboole_0(X0) | k1_xboole_0 = k7_relat_1(X1,X0)) ) | ~spl2_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f62])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    spl2_9 | ~spl2_3 | ~spl2_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f60,f39,f31,f62])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    spl2_3 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    spl2_5 <=> ! [X1,X0] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0)) ) | (~spl2_3 | ~spl2_5)),
% 0.20/0.42    inference(resolution,[],[f40,f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl2_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f31])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f39])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    spl2_8 | ~spl2_6 | ~spl2_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f53,f49,f43,f55])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl2_6 <=> v1_xboole_0(sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    spl2_7 <=> k1_xboole_0 = sK1),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    v1_xboole_0(k1_xboole_0) | (~spl2_6 | ~spl2_7)),
% 0.20/0.42    inference(backward_demodulation,[],[f45,f51])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    k1_xboole_0 = sK1 | ~spl2_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f49])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    v1_xboole_0(sK1) | ~spl2_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f43])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    spl2_7 | ~spl2_3 | ~spl2_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f47,f43,f31,f49])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    k1_xboole_0 = sK1 | (~spl2_3 | ~spl2_6)),
% 0.20/0.42    inference(resolution,[],[f32,f45])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    spl2_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f19,f43])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    v1_xboole_0(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    v1_xboole_0(sK1)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK1)),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ? [X0] : v1_xboole_0(X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    spl2_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f17,f39])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    spl2_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f16,f31])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f14,f26])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    v1_relat_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ? [X0] : (k1_xboole_0 != k7_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f6,plain,(
% 0.20/0.42    ? [X0] : (k1_xboole_0 != k7_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,negated_conjecture,(
% 0.20/0.42    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.20/0.42    inference(negated_conjecture,[],[f4])).
% 0.20/0.42  fof(f4,conjecture,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ~spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f15,f21])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (11377)------------------------------
% 0.20/0.42  % (11377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (11377)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (11377)Memory used [KB]: 6140
% 0.20/0.42  % (11377)Time elapsed: 0.005 s
% 0.20/0.42  % (11377)------------------------------
% 0.20/0.42  % (11377)------------------------------
% 0.20/0.43  % (11363)Success in time 0.065 s
%------------------------------------------------------------------------------
