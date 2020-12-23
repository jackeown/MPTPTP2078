%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   34 (  46 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   68 (  94 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f43,f46])).

fof(f46,plain,
    ( spl1_4
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f44,f32,f27,f40])).

fof(f40,plain,
    ( spl1_4
  <=> v1_xboole_0(k7_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f27,plain,
    ( spl1_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f32,plain,
    ( spl1_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f44,plain,
    ( v1_xboole_0(k7_relat_1(sK0,k1_xboole_0))
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f29,f34,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

fof(f34,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f29,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f43,plain,
    ( ~ spl1_4
    | spl1_1 ),
    inference(avatar_split_clause,[],[f37,f22,f40])).

fof(f22,plain,
    ( spl1_1
  <=> k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f37,plain,
    ( ~ v1_xboole_0(k7_relat_1(sK0,k1_xboole_0))
    | spl1_1 ),
    inference(unit_resulting_resolution,[],[f24,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f24,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f35,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f20,f32])).

fof(f20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f2])).

% (8155)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f15,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).

fof(f30,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k7_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != k7_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f25,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f14,f22])).

fof(f14,plain,(
    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:12:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (8147)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (8151)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (8151)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (8152)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (8150)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (8145)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f25,f30,f35,f43,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    spl1_4 | ~spl1_2 | ~spl1_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f44,f32,f27,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    spl1_4 <=> v1_xboole_0(k7_relat_1(sK0,k1_xboole_0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    spl1_2 <=> v1_relat_1(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    spl1_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    v1_xboole_0(k7_relat_1(sK0,k1_xboole_0)) | (~spl1_2 | ~spl1_3)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f29,f34,f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0) | ~spl1_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f32])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    v1_relat_1(sK0) | ~spl1_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f27])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ~spl1_4 | spl1_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f22,f40])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    spl1_1 <=> k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ~v1_xboole_0(k7_relat_1(sK0,k1_xboole_0)) | spl1_1),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f24,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) | spl1_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f22])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    spl1_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f20,f32])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    inference(definition_unfolding,[],[f15,f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  % (8155)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    spl1_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f13,f27])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    v1_relat_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (k1_xboole_0 != k7_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ? [X0] : (k1_xboole_0 != k7_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.22/0.49    inference(negated_conjecture,[],[f5])).
% 0.22/0.49  fof(f5,conjecture,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ~spl1_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f14,f22])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (8151)------------------------------
% 0.22/0.49  % (8151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8151)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (8151)Memory used [KB]: 6140
% 0.22/0.49  % (8151)Time elapsed: 0.059 s
% 0.22/0.49  % (8151)------------------------------
% 0.22/0.49  % (8151)------------------------------
% 0.22/0.49  % (8144)Success in time 0.127 s
%------------------------------------------------------------------------------
