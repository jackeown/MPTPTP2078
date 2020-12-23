%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :  110 ( 141 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f40,f48,f52,f58,f64,f68])).

fof(f68,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f65,f26])).

fof(f26,plain,
    ( k1_xboole_0 != k4_relat_1(k1_xboole_0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_1
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f65,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(resolution,[],[f63,f31])).

fof(f31,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k4_relat_1(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_9
  <=> ! [X0] :
        ( k1_xboole_0 = k4_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f64,plain,
    ( spl2_9
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f60,f56,f38,f62])).

fof(f38,plain,
    ( spl2_4
  <=> ! [X0] :
        ( v1_xboole_0(k4_relat_1(X0))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f56,plain,
    ( spl2_8
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f60,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k4_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(resolution,[],[f57,f39])).

fof(f39,plain,
    ( ! [X0] :
        ( v1_xboole_0(k4_relat_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f57,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f58,plain,
    ( spl2_8
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f54,f50,f46,f56])).

fof(f46,plain,
    ( spl2_6
  <=> ! [X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f50,plain,
    ( spl2_7
  <=> ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f54,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(resolution,[],[f51,f47])).

fof(f47,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f51,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f52,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f48,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f40,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

fof(f32,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f29])).

fof(f17,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f27,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f16,f24])).

fof(f16,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f6])).

fof(f6,negated_conjecture,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:12:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (29745)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.42  % (29742)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (29742)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f27,f32,f40,f48,f52,f58,f64,f68])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    spl2_1 | ~spl2_2 | ~spl2_9),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f67])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    $false | (spl2_1 | ~spl2_2 | ~spl2_9)),
% 0.20/0.42    inference(subsumption_resolution,[],[f65,f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    k1_xboole_0 != k4_relat_1(k1_xboole_0) | spl2_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    spl2_1 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl2_2 | ~spl2_9)),
% 0.20/0.42    inference(resolution,[],[f63,f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    v1_xboole_0(k1_xboole_0) | ~spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f29])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    spl2_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k4_relat_1(X0)) ) | ~spl2_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f62])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    spl2_9 <=> ! [X0] : (k1_xboole_0 = k4_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    spl2_9 | ~spl2_4 | ~spl2_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f60,f56,f38,f62])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl2_4 <=> ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    spl2_8 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k4_relat_1(X0) | ~v1_xboole_0(X0)) ) | (~spl2_4 | ~spl2_8)),
% 0.20/0.42    inference(resolution,[],[f57,f39])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0)) ) | ~spl2_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f38])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl2_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f56])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    spl2_8 | ~spl2_6 | ~spl2_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f54,f50,f46,f56])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    spl2_6 <=> ! [X0,X2] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    spl2_7 <=> ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | (~spl2_6 | ~spl2_7)),
% 0.20/0.42    inference(resolution,[],[f51,f47])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) ) | ~spl2_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f46])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) ) | ~spl2_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f50])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    spl2_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f50])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    spl2_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f20,f46])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.42    inference(rectify,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.42    inference(nnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f18,f38])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f17,f29])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    v1_xboole_0(k1_xboole_0)),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    v1_xboole_0(k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ~spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f16,f24])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.20/0.42    inference(flattening,[],[f6])).
% 0.20/0.42  fof(f6,negated_conjecture,(
% 0.20/0.42    ~k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.20/0.42    inference(negated_conjecture,[],[f5])).
% 0.20/0.42  fof(f5,conjecture,(
% 0.20/0.42    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (29742)------------------------------
% 0.20/0.42  % (29742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (29742)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (29742)Memory used [KB]: 10490
% 0.20/0.42  % (29742)Time elapsed: 0.005 s
% 0.20/0.42  % (29742)------------------------------
% 0.20/0.42  % (29742)------------------------------
% 0.20/0.43  % (29736)Success in time 0.064 s
%------------------------------------------------------------------------------
