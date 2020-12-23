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
% DateTime   : Thu Dec  3 12:48:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  87 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  129 ( 203 expanded)
%              Number of equality atoms :   49 (  83 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f36,f37,f42,f54,f62,f63,f69,f82,f89])).

fof(f89,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | spl1_6 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_2
    | spl1_6 ),
    inference(subsumption_resolution,[],[f87,f59])).

fof(f59,plain,
    ( k1_xboole_0 != sK0
    | spl1_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl1_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f87,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_1
    | ~ spl1_2 ),
    inference(subsumption_resolution,[],[f86,f26])).

fof(f26,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f86,plain,
    ( ~ v1_relat_1(sK0)
    | k1_xboole_0 = sK0
    | ~ spl1_2 ),
    inference(trivial_inequality_removal,[],[f84])).

fof(f84,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK0)
    | k1_xboole_0 = sK0
    | ~ spl1_2 ),
    inference(superposition,[],[f18,f30])).

fof(f30,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl1_2
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f82,plain,
    ( spl1_7
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f77,f39,f66])).

fof(f66,plain,
    ( spl1_7
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f39,plain,
    ( spl1_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f77,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(resolution,[],[f45,f41])).

fof(f41,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(resolution,[],[f22,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f69,plain,
    ( ~ spl1_7
    | spl1_3
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f64,f58,f33,f66])).

fof(f33,plain,
    ( spl1_3
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f64,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl1_3
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f35,f60])).

fof(f60,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f35,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f63,plain,
    ( spl1_6
    | ~ spl1_3
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f55,f24,f33,f58])).

fof(f55,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 = sK0
    | ~ spl1_1 ),
    inference(resolution,[],[f19,f26])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f54,plain,
    ( spl1_5
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f47,f39,f51])).

fof(f51,plain,
    ( spl1_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f47,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(resolution,[],[f44,f41])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f21,f20])).

fof(f21,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f42,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f37,plain,
    ( spl1_2
    | spl1_3 ),
    inference(avatar_split_clause,[],[f14,f33,f29])).

fof(f14,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
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

fof(f36,plain,
    ( ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f15,f33,f29])).

fof(f15,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 != k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f16,f24])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:49:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (32523)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.42  % (32523)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f27,f36,f37,f42,f54,f62,f63,f69,f82,f89])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    ~spl1_1 | ~spl1_2 | spl1_6),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f88])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    $false | (~spl1_1 | ~spl1_2 | spl1_6)),
% 0.21/0.42    inference(subsumption_resolution,[],[f87,f59])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    k1_xboole_0 != sK0 | spl1_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl1_6 <=> k1_xboole_0 = sK0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    k1_xboole_0 = sK0 | (~spl1_1 | ~spl1_2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f86,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    v1_relat_1(sK0) | ~spl1_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    spl1_1 <=> v1_relat_1(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    ~v1_relat_1(sK0) | k1_xboole_0 = sK0 | ~spl1_2),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f84])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK0) | k1_xboole_0 = sK0 | ~spl1_2),
% 0.21/0.42    inference(superposition,[],[f18,f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    k1_xboole_0 = k1_relat_1(sK0) | ~spl1_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    spl1_2 <=> k1_xboole_0 = k1_relat_1(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(flattening,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    spl1_7 | ~spl1_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f77,f39,f66])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl1_7 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    spl1_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_4),
% 0.21/0.42    inference(resolution,[],[f45,f41])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0) | ~spl1_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f39])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_relat_1(X0)) )),
% 0.21/0.42    inference(resolution,[],[f22,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    ~spl1_7 | spl1_3 | ~spl1_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f64,f58,f33,f66])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl1_3 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    k1_xboole_0 != k2_relat_1(k1_xboole_0) | (spl1_3 | ~spl1_6)),
% 0.21/0.42    inference(forward_demodulation,[],[f35,f60])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    k1_xboole_0 = sK0 | ~spl1_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    k1_xboole_0 != k2_relat_1(sK0) | spl1_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f33])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl1_6 | ~spl1_3 | ~spl1_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f55,f24,f33,f58])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 = sK0 | ~spl1_1),
% 0.21/0.42    inference(resolution,[],[f19,f26])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    k1_xboole_0 != sK0 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK0)),
% 0.21/0.42    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    spl1_5 | ~spl1_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f47,f39,f51])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl1_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.21/0.42    inference(resolution,[],[f44,f41])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.21/0.42    inference(resolution,[],[f21,f20])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl1_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f39])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl1_2 | spl1_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f14,f33,f29])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0] : ((k1_xboole_0 = k1_relat_1(X0) <~> k1_xboole_0 = k2_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.42    inference(negated_conjecture,[],[f6])).
% 0.21/0.42  fof(f6,conjecture,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ~spl1_2 | ~spl1_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f33,f29])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 != k1_relat_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    spl1_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f24])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    v1_relat_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (32523)------------------------------
% 0.21/0.42  % (32523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (32523)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (32523)Memory used [KB]: 10618
% 0.21/0.42  % (32523)Time elapsed: 0.006 s
% 0.21/0.42  % (32523)------------------------------
% 0.21/0.42  % (32523)------------------------------
% 0.21/0.42  % (32521)Success in time 0.064 s
%------------------------------------------------------------------------------
