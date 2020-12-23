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
% DateTime   : Thu Dec  3 12:48:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (  78 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  117 ( 177 expanded)
%              Number of equality atoms :   28 (  59 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f32,f42,f47,f53,f60,f65])).

fof(f65,plain,
    ( spl1_3
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f64,f24,f40])).

fof(f40,plain,
    ( spl1_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f24,plain,
    ( spl1_1
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f64,plain,
    ( v1_xboole_0(sK0)
    | ~ spl1_1 ),
    inference(subsumption_resolution,[],[f63,f16])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

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

fof(f63,plain,
    ( ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl1_1 ),
    inference(subsumption_resolution,[],[f62,f17])).

fof(f17,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f62,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl1_1 ),
    inference(superposition,[],[f21,f30])).

fof(f30,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f21,plain,(
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

fof(f60,plain,
    ( spl1_2
    | ~ spl1_4 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl1_2
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f58,f19])).

fof(f19,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f58,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl1_2
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f28,f46])).

fof(f46,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl1_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f28,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl1_2
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f53,plain,
    ( spl1_1
    | ~ spl1_4 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | spl1_1
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f50,f18])).

fof(f18,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl1_1
    | ~ spl1_4 ),
    inference(superposition,[],[f25,f46])).

fof(f25,plain,
    ( k1_xboole_0 != k1_relat_1(sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f47,plain,
    ( spl1_4
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f43,f40,f45])).

fof(f43,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_3 ),
    inference(resolution,[],[f41,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f41,plain,
    ( v1_xboole_0(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f42,plain,
    ( spl1_3
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f38,f27,f40])).

fof(f38,plain,
    ( v1_xboole_0(sK0)
    | ~ spl1_2 ),
    inference(subsumption_resolution,[],[f37,f16])).

fof(f37,plain,
    ( ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl1_2 ),
    inference(subsumption_resolution,[],[f35,f17])).

fof(f35,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl1_2 ),
    inference(superposition,[],[f22,f31])).

fof(f31,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f22,plain,(
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

fof(f32,plain,
    ( spl1_1
    | spl1_2 ),
    inference(avatar_split_clause,[],[f14,f27,f24])).

fof(f14,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f15,f27,f24])).

fof(f15,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 != k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:27:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (6333)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.42  % (6328)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.43  % (6327)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.43  % (6327)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f29,f32,f42,f47,f53,f60,f65])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    spl1_3 | ~spl1_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f64,f24,f40])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    spl1_3 <=> v1_xboole_0(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    spl1_1 <=> k1_xboole_0 = k1_relat_1(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    v1_xboole_0(sK0) | ~spl1_1),
% 0.20/0.43    inference(subsumption_resolution,[],[f63,f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    v1_relat_1(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ? [X0] : ((k1_xboole_0 = k1_relat_1(X0) <~> k1_xboole_0 = k2_relat_1(X0)) & v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,negated_conjecture,(
% 0.20/0.43    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.43    inference(negated_conjecture,[],[f6])).
% 0.20/0.43  fof(f6,conjecture,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    ~v1_relat_1(sK0) | v1_xboole_0(sK0) | ~spl1_1),
% 0.20/0.43    inference(subsumption_resolution,[],[f62,f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK0) | v1_xboole_0(sK0) | ~spl1_1),
% 0.20/0.43    inference(superposition,[],[f21,f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    k1_xboole_0 = k1_relat_1(sK0) | ~spl1_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f24])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.43    inference(flattening,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    spl1_2 | ~spl1_4),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f59])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    $false | (spl1_2 | ~spl1_4)),
% 0.20/0.43    inference(subsumption_resolution,[],[f58,f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    k1_xboole_0 != k2_relat_1(k1_xboole_0) | (spl1_2 | ~spl1_4)),
% 0.20/0.43    inference(forward_demodulation,[],[f28,f46])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    k1_xboole_0 = sK0 | ~spl1_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f45])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    spl1_4 <=> k1_xboole_0 = sK0),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    k1_xboole_0 != k2_relat_1(sK0) | spl1_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    spl1_2 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    spl1_1 | ~spl1_4),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    $false | (spl1_1 | ~spl1_4)),
% 0.20/0.43    inference(subsumption_resolution,[],[f50,f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (spl1_1 | ~spl1_4)),
% 0.20/0.43    inference(superposition,[],[f25,f46])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    k1_xboole_0 != k1_relat_1(sK0) | spl1_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f24])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    spl1_4 | ~spl1_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f43,f40,f45])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    k1_xboole_0 = sK0 | ~spl1_3),
% 0.20/0.43    inference(resolution,[],[f41,f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    v1_xboole_0(sK0) | ~spl1_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f40])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    spl1_3 | ~spl1_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f38,f27,f40])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    v1_xboole_0(sK0) | ~spl1_2),
% 0.20/0.43    inference(subsumption_resolution,[],[f37,f16])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ~v1_relat_1(sK0) | v1_xboole_0(sK0) | ~spl1_2),
% 0.20/0.43    inference(subsumption_resolution,[],[f35,f17])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK0) | v1_xboole_0(sK0) | ~spl1_2),
% 0.20/0.43    inference(superposition,[],[f22,f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    k1_xboole_0 = k2_relat_1(sK0) | ~spl1_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f27])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.43    inference(flattening,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    spl1_1 | spl1_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f14,f27,f24])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ~spl1_1 | ~spl1_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f15,f27,f24])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 != k1_relat_1(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (6327)------------------------------
% 0.20/0.43  % (6327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (6327)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (6327)Memory used [KB]: 10490
% 0.20/0.43  % (6327)Time elapsed: 0.006 s
% 0.20/0.43  % (6327)------------------------------
% 0.20/0.43  % (6327)------------------------------
% 0.20/0.43  % (6323)Success in time 0.073 s
%------------------------------------------------------------------------------
