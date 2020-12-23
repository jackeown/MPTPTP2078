%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  49 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   87 ( 120 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f23,f27,f31,f37,f47,f51])).

fof(f51,plain,
    ( spl0_1
    | ~ spl0_2
    | ~ spl0_7 ),
    inference(avatar_contradiction_clause,[],[f50])).

fof(f50,plain,
    ( $false
    | spl0_1
    | ~ spl0_2
    | ~ spl0_7 ),
    inference(subsumption_resolution,[],[f48,f17])).

fof(f17,plain,
    ( k1_xboole_0 != k4_relat_1(k1_xboole_0)
    | spl0_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl0_1
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_1])])).

fof(f48,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl0_2
    | ~ spl0_7 ),
    inference(resolution,[],[f46,f22])).

fof(f22,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl0_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl0_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_2])])).

fof(f46,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k4_relat_1(X0) )
    | ~ spl0_7 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl0_7
  <=> ! [X0] :
        ( k1_xboole_0 = k4_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_7])])).

fof(f47,plain,
    ( spl0_7
    | ~ spl0_3
    | ~ spl0_5 ),
    inference(avatar_split_clause,[],[f43,f35,f25,f45])).

fof(f25,plain,
    ( spl0_3
  <=> ! [X0] :
        ( v1_xboole_0(k4_relat_1(X0))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_3])])).

fof(f35,plain,
    ( spl0_5
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_5])])).

fof(f43,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k4_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl0_3
    | ~ spl0_5 ),
    inference(resolution,[],[f36,f26])).

fof(f26,plain,
    ( ! [X0] :
        ( v1_xboole_0(k4_relat_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl0_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f36,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl0_5 ),
    inference(avatar_component_clause,[],[f35])).

fof(f37,plain,
    ( spl0_5
    | ~ spl0_2
    | ~ spl0_4 ),
    inference(avatar_split_clause,[],[f32,f29,f20,f35])).

fof(f29,plain,
    ( spl0_4
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | X0 = X1
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_4])])).

fof(f32,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl0_2
    | ~ spl0_4 ),
    inference(resolution,[],[f30,f22])).

fof(f30,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | X0 = X1
        | ~ v1_xboole_0(X0) )
    | ~ spl0_4 ),
    inference(avatar_component_clause,[],[f29])).

fof(f31,plain,(
    spl0_4 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f27,plain,(
    spl0_3 ),
    inference(avatar_split_clause,[],[f12,f25])).

fof(f12,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k4_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

fof(f23,plain,(
    spl0_2 ),
    inference(avatar_split_clause,[],[f11,f20])).

fof(f11,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f18,plain,(
    ~ spl0_1 ),
    inference(avatar_split_clause,[],[f10,f15])).

fof(f10,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f5])).

fof(f5,negated_conjecture,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:07:37 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.22/0.41  % (11372)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.42  % (11375)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (11379)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.42  % (11379)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f18,f23,f27,f31,f37,f47,f51])).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    spl0_1 | ~spl0_2 | ~spl0_7),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f50])).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    $false | (spl0_1 | ~spl0_2 | ~spl0_7)),
% 0.22/0.42    inference(subsumption_resolution,[],[f48,f17])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    k1_xboole_0 != k4_relat_1(k1_xboole_0) | spl0_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    spl0_1 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl0_1])])).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl0_2 | ~spl0_7)),
% 0.22/0.42    inference(resolution,[],[f46,f22])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0) | ~spl0_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f20])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    spl0_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl0_2])])).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k4_relat_1(X0)) ) | ~spl0_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f45])).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    spl0_7 <=> ! [X0] : (k1_xboole_0 = k4_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl0_7])])).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    spl0_7 | ~spl0_3 | ~spl0_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f43,f35,f25,f45])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    spl0_3 <=> ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl0_3])])).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    spl0_5 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl0_5])])).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k4_relat_1(X0) | ~v1_xboole_0(X0)) ) | (~spl0_3 | ~spl0_5)),
% 0.22/0.42    inference(resolution,[],[f36,f26])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0)) ) | ~spl0_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f25])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl0_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f35])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    spl0_5 | ~spl0_2 | ~spl0_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f32,f29,f20,f35])).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    spl0_4 <=> ! [X1,X0] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl0_4])])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | (~spl0_2 | ~spl0_4)),
% 0.22/0.42    inference(resolution,[],[f30,f22])).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) ) | ~spl0_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f29])).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    spl0_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f13,f29])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    spl0_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f12,f25])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k4_relat_1(X0)))),
% 0.22/0.42    inference(pure_predicate_removal,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    spl0_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f11,f20])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ~spl0_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f10,f15])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,plain,(
% 0.22/0.42    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(flattening,[],[f5])).
% 0.22/0.42  fof(f5,negated_conjecture,(
% 0.22/0.42    ~k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(negated_conjecture,[],[f4])).
% 0.22/0.42  fof(f4,conjecture,(
% 0.22/0.42    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (11379)------------------------------
% 0.22/0.42  % (11379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (11379)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (11379)Memory used [KB]: 6012
% 0.22/0.42  % (11379)Time elapsed: 0.003 s
% 0.22/0.42  % (11379)------------------------------
% 0.22/0.42  % (11379)------------------------------
% 0.22/0.42  % (11368)Success in time 0.063 s
%------------------------------------------------------------------------------
