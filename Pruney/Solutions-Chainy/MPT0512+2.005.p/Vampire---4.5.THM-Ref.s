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
% DateTime   : Thu Dec  3 12:48:43 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   43 (  59 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :  108 ( 153 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f32,f36,f44,f50,f56,f64])).

fof(f64,plain,
    ( spl1_1
    | ~ spl1_3
    | ~ spl1_8 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | spl1_1
    | ~ spl1_3
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f61,f21])).

fof(f21,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl1_1
  <=> k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f61,plain,
    ( k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_8 ),
    inference(resolution,[],[f55,f31])).

fof(f31,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl1_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl1_8
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f56,plain,
    ( spl1_8
    | ~ spl1_2
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f51,f48,f24,f54])).

fof(f24,plain,
    ( spl1_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f48,plain,
    ( spl1_7
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_relat_1(X1)
        | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f51,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) )
    | ~ spl1_2
    | ~ spl1_7 ),
    inference(resolution,[],[f49,f26])).

fof(f26,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_xboole_0(X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f50,plain,
    ( spl1_7
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f46,f42,f34,f48])).

fof(f34,plain,
    ( spl1_4
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f42,plain,
    ( spl1_6
  <=> ! [X1,X0] :
        ( v1_xboole_0(k7_relat_1(X0,X1))
        | ~ v1_xboole_0(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_relat_1(X1)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k7_relat_1(X0,X1))
        | ~ v1_xboole_0(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f42])).

fof(f44,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
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

fof(f36,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f15,f34])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f32,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f14,f29])).

fof(f14,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f27,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f12,f24])).

fof(f12,plain,(
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

fof(f22,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f13,f19])).

fof(f13,plain,(
    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:15:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.40  % (4700)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.12/0.40  % (4698)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.12/0.40  % (4699)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.12/0.40  % (4698)Refutation found. Thanks to Tanya!
% 0.12/0.40  % SZS status Theorem for theBenchmark
% 0.12/0.40  % SZS output start Proof for theBenchmark
% 0.12/0.40  fof(f65,plain,(
% 0.12/0.40    $false),
% 0.12/0.40    inference(avatar_sat_refutation,[],[f22,f27,f32,f36,f44,f50,f56,f64])).
% 0.12/0.40  fof(f64,plain,(
% 0.12/0.40    spl1_1 | ~spl1_3 | ~spl1_8),
% 0.12/0.40    inference(avatar_contradiction_clause,[],[f63])).
% 0.12/0.40  fof(f63,plain,(
% 0.12/0.40    $false | (spl1_1 | ~spl1_3 | ~spl1_8)),
% 0.12/0.40    inference(subsumption_resolution,[],[f61,f21])).
% 0.12/0.40  fof(f21,plain,(
% 0.12/0.40    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) | spl1_1),
% 0.12/0.40    inference(avatar_component_clause,[],[f19])).
% 0.12/0.41  fof(f19,plain,(
% 0.12/0.41    spl1_1 <=> k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0)),
% 0.12/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.12/0.41  fof(f61,plain,(
% 0.12/0.41    k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0) | (~spl1_3 | ~spl1_8)),
% 0.12/0.41    inference(resolution,[],[f55,f31])).
% 0.12/0.41  fof(f31,plain,(
% 0.12/0.41    v1_xboole_0(k1_xboole_0) | ~spl1_3),
% 0.12/0.41    inference(avatar_component_clause,[],[f29])).
% 0.12/0.41  fof(f29,plain,(
% 0.12/0.41    spl1_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.12/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.12/0.41  fof(f55,plain,(
% 0.12/0.41    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k7_relat_1(sK0,X0)) ) | ~spl1_8),
% 0.12/0.41    inference(avatar_component_clause,[],[f54])).
% 0.12/0.41  fof(f54,plain,(
% 0.12/0.41    spl1_8 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k7_relat_1(sK0,X0))),
% 0.12/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.12/0.41  fof(f56,plain,(
% 0.12/0.41    spl1_8 | ~spl1_2 | ~spl1_7),
% 0.12/0.41    inference(avatar_split_clause,[],[f51,f48,f24,f54])).
% 0.12/0.41  fof(f24,plain,(
% 0.12/0.41    spl1_2 <=> v1_relat_1(sK0)),
% 0.12/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.12/0.41  fof(f48,plain,(
% 0.12/0.41    spl1_7 <=> ! [X1,X0] : (~v1_xboole_0(X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0))),
% 0.12/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.12/0.41  fof(f51,plain,(
% 0.12/0.41    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k7_relat_1(sK0,X0)) ) | (~spl1_2 | ~spl1_7)),
% 0.12/0.41    inference(resolution,[],[f49,f26])).
% 0.12/0.41  fof(f26,plain,(
% 0.12/0.41    v1_relat_1(sK0) | ~spl1_2),
% 0.12/0.41    inference(avatar_component_clause,[],[f24])).
% 0.12/0.41  fof(f49,plain,(
% 0.12/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_xboole_0(X0) | k1_xboole_0 = k7_relat_1(X1,X0)) ) | ~spl1_7),
% 0.12/0.41    inference(avatar_component_clause,[],[f48])).
% 0.12/0.41  fof(f50,plain,(
% 0.12/0.41    spl1_7 | ~spl1_4 | ~spl1_6),
% 0.12/0.41    inference(avatar_split_clause,[],[f46,f42,f34,f48])).
% 0.12/0.41  fof(f34,plain,(
% 0.12/0.41    spl1_4 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.12/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.12/0.41  fof(f42,plain,(
% 0.12/0.41    spl1_6 <=> ! [X1,X0] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 0.12/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.12/0.41  fof(f46,plain,(
% 0.12/0.41    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0)) ) | (~spl1_4 | ~spl1_6)),
% 0.12/0.41    inference(resolution,[],[f43,f35])).
% 0.12/0.41  fof(f35,plain,(
% 0.12/0.41    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl1_4),
% 0.12/0.41    inference(avatar_component_clause,[],[f34])).
% 0.12/0.41  fof(f43,plain,(
% 0.12/0.41    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) ) | ~spl1_6),
% 0.12/0.41    inference(avatar_component_clause,[],[f42])).
% 0.12/0.41  fof(f44,plain,(
% 0.12/0.41    spl1_6),
% 0.12/0.41    inference(avatar_split_clause,[],[f16,f42])).
% 0.12/0.41  fof(f16,plain,(
% 0.12/0.41    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f9])).
% 0.12/0.41  fof(f9,plain,(
% 0.12/0.41    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 0.12/0.41    inference(flattening,[],[f8])).
% 0.12/0.41  fof(f8,plain,(
% 0.12/0.41    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 0.12/0.41    inference(ennf_transformation,[],[f3])).
% 0.12/0.41  fof(f3,axiom,(
% 0.12/0.41    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))))),
% 0.12/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).
% 0.12/0.41  fof(f36,plain,(
% 0.12/0.41    spl1_4),
% 0.12/0.41    inference(avatar_split_clause,[],[f15,f34])).
% 0.12/0.41  fof(f15,plain,(
% 0.12/0.41    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f7])).
% 0.12/0.41  fof(f7,plain,(
% 0.12/0.41    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.12/0.41    inference(ennf_transformation,[],[f2])).
% 0.12/0.41  fof(f2,axiom,(
% 0.12/0.41    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.12/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.12/0.41  fof(f32,plain,(
% 0.12/0.41    spl1_3),
% 0.12/0.41    inference(avatar_split_clause,[],[f14,f29])).
% 0.12/0.41  fof(f14,plain,(
% 0.12/0.41    v1_xboole_0(k1_xboole_0)),
% 0.12/0.41    inference(cnf_transformation,[],[f1])).
% 0.12/0.41  fof(f1,axiom,(
% 0.12/0.41    v1_xboole_0(k1_xboole_0)),
% 0.12/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.12/0.41  fof(f27,plain,(
% 0.12/0.41    spl1_2),
% 0.12/0.41    inference(avatar_split_clause,[],[f12,f24])).
% 0.12/0.41  fof(f12,plain,(
% 0.12/0.41    v1_relat_1(sK0)),
% 0.12/0.41    inference(cnf_transformation,[],[f11])).
% 0.12/0.41  fof(f11,plain,(
% 0.12/0.41    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0)),
% 0.12/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).
% 0.12/0.41  fof(f10,plain,(
% 0.12/0.41    ? [X0] : (k1_xboole_0 != k7_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0))),
% 0.12/0.41    introduced(choice_axiom,[])).
% 0.12/0.41  fof(f6,plain,(
% 0.12/0.41    ? [X0] : (k1_xboole_0 != k7_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.12/0.41    inference(ennf_transformation,[],[f5])).
% 0.12/0.41  fof(f5,negated_conjecture,(
% 0.12/0.41    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.12/0.41    inference(negated_conjecture,[],[f4])).
% 0.12/0.41  fof(f4,conjecture,(
% 0.12/0.41    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.12/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 0.12/0.41  fof(f22,plain,(
% 0.12/0.41    ~spl1_1),
% 0.12/0.41    inference(avatar_split_clause,[],[f13,f19])).
% 0.12/0.41  fof(f13,plain,(
% 0.12/0.41    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)),
% 0.12/0.41    inference(cnf_transformation,[],[f11])).
% 0.12/0.41  % SZS output end Proof for theBenchmark
% 0.12/0.41  % (4698)------------------------------
% 0.12/0.41  % (4698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.41  % (4698)Termination reason: Refutation
% 0.12/0.41  
% 0.12/0.41  % (4698)Memory used [KB]: 10490
% 0.12/0.41  % (4698)Time elapsed: 0.005 s
% 0.12/0.41  % (4698)------------------------------
% 0.12/0.41  % (4698)------------------------------
% 0.20/0.41  % (4692)Success in time 0.062 s
%------------------------------------------------------------------------------
